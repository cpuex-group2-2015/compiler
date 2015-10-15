type closure = { entry : Id.l; actual_fv : Id.t list }
type t = (* クロージャ変換後の式 (caml2html: closure_t) *)
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.l
type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }
type prog = Prog of fundef list * t

let rec fv = function
  | Unit | Int(_) | Float(_) | ExtArray(_) -> S.empty
  | Neg(x) | FNeg(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> S.remove x (S.union (S.of_list ys) (fv e))
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))
  | Put(x, y, z) -> S.of_list [x; y; z]

let toplevel : fundef list ref = ref []

let rec g env known = function (* クロージャ変換ルーチン本体 (caml2html: closure_g) *)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (M.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* 関数定義の場合 (caml2html: closure_letrec) *)
      (* 関数定義let rec x y1 ... yn = e1 in e2の場合は、
         xに自由変数がない(closureを介さずdirectに呼び出せる)
         と仮定し、knownに追加してe1をクロージャ変換してみる *)
      let toplevel_backup = !toplevel in
      let env' = M.add x t env in
      let known' = S.add x known in
      let e1' = g (M.add_list yts env') known' e1 in
      (* 本当に自由変数がなかったか、変換結果e1'を確認する *)
      (* 注意: e1'にx自身が変数として出現する場合はclosureが必要!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照) *)
      let zs = S.diff (fv e1') (S.of_list (List.map fst yts)) in
      let known', e1' =
	if S.is_empty zs then known', e1' else
	(* 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す *)
	(Format.eprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
	 Format.eprintf "function %s cannot be directly applied in fact@." x;
	 toplevel := toplevel_backup;
	 let e1' = g (M.add_list yts env') known e1 in
	 known, e1') in
      let zs = S.elements (S.diff (fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* 自由変数のリスト *)
      let zts = List.map (fun z -> (z, M.find z env')) zs in (* ここで自由変数zの型を引くために引数envが必要 *)
      toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* トップレベル関数を追加 *)
      let e2' = g env' known' e2 in
      if S.mem x (fv e2') then (* xが変数としてe2'に出現するか *)
	MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2') (* 出現していたら削除しない *)
      else
	(Format.eprintf "eliminating closure(s) %s@." x;
	 e2') (* 出現しなければMakeClsを削除 *)
  | KNormal.App(x, ys) when S.mem x known -> (* 関数適用の場合 (caml2html: closure_app) *)
      Format.eprintf "directly applying %s@." x;
      AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> AppCls(f, xs)
  | KNormal.Tuple(xs) -> Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(Id.L(x))
  | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("min_caml_" ^ x), ys)

let rec arg_list_to_string string list =
  match list with
  | [] -> string
  | (x,t)::ys -> arg_list_to_string (string ^ x ^ ":" ^ (Type.type_to_string t) ^ " ") ys

let rec show_content indent t = match t with
  | Unit -> print_string (indent ^ "()\n")
  | Int(i) -> print_string (string_of_int i)
  | Float(f) -> print_string (string_of_float f)
  | Neg(x) | FNeg(x) -> print_string ("- " ^ x)
  | Add(x, y) -> print_string (x ^ " + " ^ y)
  | Sub(x, y) -> print_string (x ^ " - " ^ y)
  | FAdd(x, y) -> print_string (x ^ " .+ " ^ y)
  | FSub(x, y) -> print_string (x ^ " .- " ^ y)
  | FMul(x, y) -> print_string (x ^ " .* " ^ y)
  | FDiv(x, y) -> print_string (x ^ " ./ " ^ y)
  | IfEq(x, y, e1, e2) ->
     print_string (indent ^ "if " ^ x ^ " = " ^ y ^ " then\n");
     (match e1 with
      | Int(_) | Float(_) | Neg(_) | Add(_, _) | Sub(_, _) | FAdd(_, _) | FSub(_, _) | FMul(_, _) | FDiv(_, _) | Var(_) | Tuple(_) | Get(_, _) | Put(_, _, _) | AppCls(_, _) | AppDir(_, _) ->
        print_string (indent ^ "  "); show_content "" e1; print_string "\n"
      | _ -> show_content (indent ^ "  ") e1);
     print_string (indent ^ "else\n");
     (match e2 with
      | Int(_) | Float(_) | Neg(_) | Add(_, _) | Sub(_, _) | FAdd(_, _) | FSub(_, _) | FMul(_, _) | FDiv(_, _) | Var(_) | Tuple(_) | Get(_, _) | Put(_, _, _) | AppCls(_, _) | AppDir(_, _) ->
        print_string (indent ^ "  "); show_content "" e2; print_string "\n"
      | _ -> show_content (indent ^ "  ") e2)
  | IfLE(x, y, e1, e2) ->
     print_string (indent ^ "if " ^ x ^ " < " ^ y ^ " then\n");
     (match e1 with
      | Int(_) | Float(_) | Neg(_) | Add(_, _) | Sub(_, _) | FAdd(_, _) | FSub(_, _) | FMul(_, _) | FDiv(_, _) | Var(_) | Tuple(_) | Get(_, _) | Put(_, _, _) | AppCls(_, _) | AppDir(_, _) ->
        print_string (indent ^ "  "); show_content "" e1; print_string "\n"
      | _ -> show_content (indent ^ "  ") e1);
     print_string (indent ^ "else\n");
     (match e2 with
      | Int(_) | Float(_) | Neg(_) | Add(_, _) | Sub(_, _) | FAdd(_, _) | FSub(_, _) | FMul(_, _) | FDiv(_, _) | Var(_) | Tuple(_) | Get(_, _) | Put(_, _, _) | AppCls(_, _) | AppDir(_, _) ->
        print_string (indent ^ "  "); show_content "" e2; print_string "\n"
      | _ -> show_content (indent ^ "  ") e2)
  | Let((x, t), e1, e2) ->
     print_string (indent ^ "let " ^ x ^ ":" ^ (Type.type_to_string t) ^ " = ");
     (match e1 with
      | Int(_) | Float(_) | Neg(_) | Add(_, _) | Sub(_, _) | FAdd(_, _) | FSub(_, _) | FMul(_, _) | FDiv(_, _) | Var(_) | Tuple(_) | Get(_, _) | Put(_, _, _) | AppCls(_, _) | AppDir(_, _) ->
        show_content "" e1; print_string " in\n"
      | _ -> print_string "\n"; show_content (indent ^ "  ") e1; print_string (indent ^ "in\n"));
     (match e2 with
      | Int(_) | Float(_) | Neg(_) | Add(_, _) | Sub(_, _) | FAdd(_, _) | FSub(_, _) | FMul(_, _) | FDiv(_, _) | Var(_) | Tuple(_) | Get(_, _) | Put(_, _, _) | AppCls(_, _) | AppDir(_, _) ->
        print_string indent; show_content "" e2; print_string "\n"
      | _ -> show_content indent e2)
  | Var(x) -> print_string x
  | MakeCls((x, t), { entry=Id.L(l); actual_fv=xs }, body) ->
     print_string (indent ^ "make_closure " ^ x ^ ":" ^ (Type.type_to_string t) ^ "=(" ^ l ^ ",(" ^ (String.concat "," xs) ^ ")) in\n");
     show_content (indent ^ "  ") body
  | AppCls(x, ys) -> print_string ("apply_closure(" ^ x ^ ", " ^ (String.concat "," ys) ^ ")")
  | AppDir(Id.L(l), ys) -> print_string ("apply_direct(" ^ l ^ ", " ^ (String.concat "," ys) ^ ")")
  | Tuple(xs) -> print_string ("(" ^ (String.concat "," xs) ^ ")")
  | LetTuple(args, x, e) ->
     print_string (indent ^ "let (" ^ (arg_list_to_string "" args) ^ ") = " ^ x ^ " in\n");
     show_content (indent ^ "  ") e
  | Get(x, y) -> print_string (x ^ ".(" ^ y ^ ")")
  | Put(x, y, z) -> print_string (x ^ ".(" ^ y ^ ") <- " ^ z)
  | ExtArray(Id.L(l)) -> print_string (indent ^ "ExtArray " ^ l ^ "\n")

let show_fundef { name = (Id.L(x), t); args = args; formal_fv = fvs; body } =
  print_string ("\tFunction " ^ x ^ " (" ^ (arg_list_to_string " "args) ^ ") =" ^ (Type.type_to_string t) ^ "\n");
  print_string ("\t  Free variables: (" ^ (arg_list_to_string " " fvs) ^ ")\n");
  show_content "\t  " body

let show_prog (Prog(fs, body)) =
  print_string "\t-----Top Level Functions-----\n";
  List.iter show_fundef fs;
  print_string "\t-----Main Routine-----\n";
  show_content "\t" body;
  print_string "=======================\n"

let f e =
  toplevel := [];
  let e' = g M.empty S.empty e in
  let tmp = Prog(List.rev !toplevel, e') in
  print_string "=======================\n";
  print_string "\tClosure.Prog\n";
  print_string "=======================\n";
  show_prog tmp;
  tmp
