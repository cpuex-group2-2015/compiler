open Asm

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"

let file = ref ""
let address = ref 0
let address_list = Hashtbl.create 0

let stackset = ref S.empty (* すでに Save された変数の集合 *)
let stackmap = ref [] (* Save された変数のスタックにおける位置 *)
let save x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    (let pad =
       if List.length !stackmap mod 2 = 0 then [] else [Id.gentmp Type.Int] in
       stackmap := !stackmap @ pad @ [x; x])
let locate x =
  let rec loc = function
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
    loc !stackmap
let offset x = 4 * List.hd (locate x)
let stacksize () = align ((List.length !stackmap + 1) * 4)

let reg r =
  if is_reg r
  then String.sub r 1 (String.length r - 1)
  else r

let load_label r label =
  "\tlis\t" ^ (reg r) ^ ", ha16(" ^ label ^ ")\n" ^
  "\taddi\t" ^ (reg r) ^ ", " ^ (reg r) ^ ", lo16(" ^ label ^ ")\n"

(* 関数呼び出しのために引数を並べ替える (register shuffling) *)
let rec shuffle sw xys =
  (* remove identical moves *)
  let (_, xys) = List.partition (fun (x, y) -> x = y) xys in
    (* find acyclic moves *)
    match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
      | ([], []) -> []
      | ((x, y) :: xys, []) -> (* no acyclic moves; resolve a cyclic move *)
	  (y, sw) :: (x, y) ::
	    shuffle sw (List.map (function
				    | (y', z) when y = y' -> (sw, z)
				    | yz -> yz) xys)
      | (xys, acyc) -> acyc @ shuffle sw xys

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)

let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 *)
    (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  | (NonTail(x), Li(i)) when i >= -32768 && i < 32768 ->
      file := !file ^ Printf.sprintf "\tli\t%s, %d\n" (reg x) i;
      address := !address + 1
  | (NonTail(x), Li(i)) ->
      let n = i lsr 16 in
      let m = i lxor (n lsl 16) in
      let r = reg x in
	file := !file ^ Printf.sprintf "\tlis\t%s, %d\n" r n;
	file := !file ^ Printf.sprintf "\tori\t%s, %s, %d\n" r r m;
	address := !address + 2
  | (NonTail(x), FLi(Id.L(l))) ->
      let s = load_label reg_tmp l in
      file := !file ^ Printf.sprintf "%s\tlfd\t%s, 0(%s)\n" s (reg x) reg_tmp;
      address := !address + 1
  | (NonTail(x), SetL(Id.L(y))) ->
      let s = load_label x y in
      file := !file ^ Printf.sprintf "%s" s;
      address := !address + 1
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) ->
     file := !file ^ Printf.sprintf "\tmr\t%s, %s\n" (reg x) (reg y);
     address := !address + 1
  | (NonTail(x), Neg(y)) ->
     file := !file ^ Printf.sprintf "\tneg\t%s, %s\n" (reg x) (reg y);
     address := !address + 1
  | (NonTail(x), Add(y, V(z))) ->
      file := !file ^ Printf.sprintf "\tadd\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), Add(y, C(z))) ->
      file := !file ^ Printf.sprintf "\taddi\t%s, %s, %d\n" (reg x) (reg y) z;
      address := !address + 1
  | (NonTail(x), Sub(y, V(z))) ->
      file := !file ^ Printf.sprintf "\tsub\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), Sub(y, C(z))) ->
      file := !file ^ Printf.sprintf "\tsubi\t%s, %s, %d\n" (reg x) (reg y) z;
      address := !address + 1
  | (NonTail(x), Slw(y, V(z))) ->
      file := !file ^ Printf.sprintf "\tslw\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), Slw(y, C(z))) ->
      file := !file ^ Printf.sprintf "\tslwi\t%s, %s, %d\n" (reg x) (reg y) z;
      address := !address + 1
  | (NonTail(x), Lwz(y, V(z))) ->
      file := !file ^ Printf.sprintf "\tlwzx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), Lwz(y, C(z))) ->
      file := !file ^ Printf.sprintf "\tlwz\t%s, %d(%s)\n" (reg x) z (reg y);
      address := !address + 1
  | (NonTail(_), Stw(x, y, V(z))) ->
      file := !file ^ Printf.sprintf "\tstwx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(_), Stw(x, y, C(z))) ->
      file := !file ^ Printf.sprintf "\tstw\t%s, %d(%s)\n" (reg x) z (reg y);
      address := !address + 1
  | (NonTail(x), FMr(y)) when x = y -> ()
  | (NonTail(x), FMr(y)) ->
     file := !file ^ Printf.sprintf "\tfmr\t%s, %s\n" (reg x) (reg y);
     address := !address + 1
  | (NonTail(x), FNeg(y)) ->
      file := !file ^ Printf.sprintf "\tfneg\t%s, %s\n" (reg x) (reg y);
      address := !address + 1
  | (NonTail(x), FAdd(y, z)) ->
      file := !file ^ Printf.sprintf "\tfadd\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), FSub(y, z)) ->
      file := !file ^ Printf.sprintf "\tfsub\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), FMul(y, z)) ->
      file := !file ^ Printf.sprintf "\tfmul\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), FDiv(y, z)) ->
      file := !file ^ Printf.sprintf "\tfdiv\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), Lfd(y, V(z))) ->
      file := !file ^ Printf.sprintf "\tlfdx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(x), Lfd(y, C(z))) ->
      file := !file ^ Printf.sprintf "\tlfd\t%s, %d(%s)\n" (reg x) z (reg y);
      address := !address + 1
  | (NonTail(_), Stfd(x, y, V(z))) ->
      file := !file ^ Printf.sprintf "\tstfdx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      address := !address + 1
  | (NonTail(_), Stfd(x, y, C(z))) ->
      file := !file ^ Printf.sprintf "\tstfd\t%s, %d(%s)\n" (reg x) z (reg y);
      address := !address + 1
  | (NonTail(_), Comment(s)) ->
     file := !file ^ Printf.sprintf "#\t%s\n" s;
     address := !address + 1
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
      when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
	file := !file ^ Printf.sprintf "\tstw\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
	address := !address + 1
  | (NonTail(_), Save(x, y))
      when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
	file := !file ^ Printf.sprintf "\tstfd\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
	address := !address + 1
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
      file := !file ^ Printf.sprintf "\tlwz\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
      address := !address + 1
  | (NonTail(x), Restore(y)) ->
      assert (List.mem x allfregs);
      file := !file ^ Printf.sprintf "\tlfd\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
      address := !address + 1
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Comment _ | Save _ as exp)) ->
      g' oc (NonTail(Id.gentmp Type.Unit), exp);
      file := !file ^ Printf.sprintf "\tblr\n";
      address := !address + 1
  | (Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | Slw _ |
            Lwz _ as exp)) ->
      g' oc (NonTail(regs.(0)), exp);
      file := !file ^ Printf.sprintf "\tblr\n";
      address := !address + 1
  | (Tail, (FLi _ | FMr _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ |
            Lfd _ as exp)) ->
      g' oc (NonTail(fregs.(0)), exp);
      file := !file ^ Printf.sprintf "\tblr\n";
      address := !address + 1
  | (Tail, (Restore(x) as exp)) ->
      (match locate x with
	 | [i] -> g' oc (NonTail(regs.(0)), exp)
	 | [i; j] when (i + 1 = j) -> g' oc (NonTail(fregs.(0)), exp)
	 | _ -> assert false);
      file := !file ^ Printf.sprintf "\tblr\n";
      address := !address + 1
  | (Tail, IfEq(x, V(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_tail_if oc e1 e2 "beq" "bne"
  | (Tail, IfEq(x, C(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      address := !address + 1;
      g'_tail_if oc e1 e2 "beq" "bne"
  | (Tail, IfLE(x, V(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_tail_if oc e1 e2 "ble" "bgt"
  | (Tail, IfLE(x, C(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      address := !address + 1;
      g'_tail_if oc e1 e2 "ble" "bgt"
  | (Tail, IfGE(x, V(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_tail_if oc e1 e2 "bge" "blt"
  | (Tail, IfGE(x, C(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      address := !address + 1;
      g'_tail_if oc e1 e2 "bge" "blt"
  | (Tail, IfFEq(x, y, e1, e2)) ->
      file := !file ^ Printf.sprintf "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_tail_if oc e1 e2 "beq" "bne"
  | (Tail, IfFLE(x, y, e1, e2)) ->
      file := !file ^ Printf.sprintf "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_tail_if oc e1 e2 "ble" "bgt"
  | (NonTail(z), IfEq(x, V(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne"
  | (NonTail(z), IfEq(x, C(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne"
  | (NonTail(z), IfLE(x, V(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt"
  | (NonTail(z), IfLE(x, C(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt"
  | (NonTail(z), IfGE(x, V(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpw\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt"
  | (NonTail(z), IfGE(x, C(y), e1, e2)) ->
      file := !file ^ Printf.sprintf "\tcmpwi\tcr7, %s, %d\n" (reg x) y;
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt"
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
      file := !file ^ Printf.sprintf "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne"
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
      file := !file ^ Printf.sprintf "\tfcmpu\tcr7, %s, %s\n" (reg x) (reg y);
      address := !address + 1;
      g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt"
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [(x, reg_cl)] ys zs;
      file := !file ^ Printf.sprintf "\tlwz\t%s, 0(%s)\n" (reg reg_sw) (reg reg_cl);
      file := !file ^ Printf.sprintf "\tmtctr\t%s\n\tbctr\n" (reg reg_sw);
      address := !address + 2;
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
      g'_args oc [] ys zs;
      file := !file ^ Printf.sprintf "\tb\t%s\n" x;
      address := !address + 1
  | (NonTail(a), CallCls(x, ys, zs)) ->
      file := !file ^ Printf.sprintf "\tmflr\t%s\n" reg_tmp;
      address := !address + 1;
      g'_args oc [(x, reg_cl)] ys zs;
      let ss = stacksize () in
	file := !file ^ Printf.sprintf "\tstw\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
	file := !file ^ Printf.sprintf "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
	file := !file ^ Printf.sprintf "\tlwz\t%s, 0(%s)\n" reg_tmp (reg reg_cl);
	file := !file ^ Printf.sprintf "\tmtctr\t%s\n" reg_tmp;
	file := !file ^ Printf.sprintf "\tbctrl\n";
	file := !file ^ Printf.sprintf "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
	file := !file ^ Printf.sprintf "\tlwz\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
	address := !address + 7;
	(if List.mem a allregs && a <> regs.(0) then
	  (file := !file ^ Printf.sprintf "\tmr\t%s, %s\n" (reg a) (reg regs.(0));
	   address := !address + 1)
	 else if List.mem a allfregs && a <> fregs.(0) then
	  (file := !file ^ Printf.sprintf "\tfmr\t%s, %s\n" (reg a) (reg fregs.(0));
	   address := !address + 1));
	file := !file ^ Printf.sprintf "\tmtlr\t%s\n" reg_tmp;
	address := !address + 1
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) ->
      file := !file ^ Printf.sprintf "\tmflr\t%s\n" reg_tmp;
      address := !address + 1;
      g'_args oc [] ys zs;
      let ss = stacksize () in
	file := !file ^ Printf.sprintf "\tstw\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
	file := !file ^ Printf.sprintf "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
	file := !file ^ Printf.sprintf "\tbl\t%d\n" (Hashtbl.find address_list x);
	file := !file ^ Printf.sprintf "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
	file := !file ^ Printf.sprintf "\tlwz\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
	address := !address + 5;
	(if List.mem a allregs && a <> regs.(0) then
	  (file := !file ^ Printf.sprintf "\tmr\t%s, %s\n" (reg a) (reg regs.(0));
	   address := !address + 1)
	 else if List.mem a allfregs && a <> fregs.(0) then
	  (file := !file ^ Printf.sprintf "\tfmr\t%s, %s\n" (reg a) (reg fregs.(0));
	   address := !address + 1));
	file := !file ^ Printf.sprintf "\tmtlr\t%s\n" reg_tmp;
	address := !address + 1
and g'_tail_if oc e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
    file := !file ^ Printf.sprintf "\t%s\tcr7, %s\n" bn b_else;
    address := !address + 1;
    let stackset_back = !stackset in
      g oc (Tail, e1);
      (*file := !file ^ Printf.sprintf "%s:\n" b_else;*)
      file := Str.global_replace (Str.regexp b_else) (string_of_int !address) !file;
      stackset := stackset_back;
      g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
    file := !file ^ Printf.sprintf "\t%s\tcr7, %s\n" bn b_else;
    address := !address + 1;
    let stackset_back = !stackset in
      g oc (dest, e1);
      let stackset1 = !stackset in
	file := !file ^ Printf.sprintf "\tb\t%s\n" b_cont;
	file := !file ^ Printf.sprintf "%s:\n" b_else;
	address := !address + 2;
	stackset := stackset_back;
	g oc (dest, e2);
	file := !file ^ Printf.sprintf "%s:\n" b_cont;
	address := !address + 1;
	let stackset2 = !stackset in
	  stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys zs =
  let (i, yrs) =
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl) ys in
    List.iter
      (fun (y, r) -> (file := !file ^ Printf.sprintf "\tmr\t%s, %s\n" (reg r) (reg y); address := !address + 1))
      (shuffle reg_sw yrs);
    let (d, zfrs) =
      List.fold_left
	(fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
	(0, []) zs in
      List.iter
        (fun (z, fr) -> (file := !file ^ Printf.sprintf "\tfmr\t%s, %s\n" (reg fr) (reg z); address := !address + 1))
	(shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  stackset := S.empty;
  stackmap := [];
  Hashtbl.add address_list x !address;
  g oc (Tail, e)

(* let f oc (Prog(data, fundefs, e)) = *)
let f oc p =
  show_asm_prog "  " p;
  let Prog(data, fundefs, e) = p in
  Format.eprintf "generating assembly...@.";
  (if data <> [] then
    (file := !file ^ Printf.sprintf "\t.data\n\t.literal8\n";
     List.iter
       (fun (Id.L(x), d) ->
	 file := !file ^ Printf.sprintf "\t.align 3\n";
	 file := !file ^ Printf.sprintf "%s:\t # %f\n" x d;
	 file := !file ^ Printf.sprintf "\t.long\t%ld\n" (gethi d);
	 file := !file ^ Printf.sprintf "\t.long\t%ld\n" (getlo d))
       data));
  List.iter (fun fundef -> h oc fundef) fundefs;
  stackset := S.empty;
  stackmap := [];
  print_string ("main entry point address " ^ (string_of_int !address) ^ "\n");
  g oc (NonTail("_R_0"), e);
  print_string ("all lines " ^ (string_of_int !address) ^ "\n");
  Printf.fprintf oc "%s" !file
