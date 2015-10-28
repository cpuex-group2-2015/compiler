open Asm

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"

let file = ref ""
let address = ref 0
let address_list = Hashtbl.create 0

let rec int_to_binary int digit res =
  if int > 0 then
    int_to_binary (int / 2) (digit - 1) ((string_of_int (int mod 2)) ^ res)
  else if digit > 0 then
    int_to_binary int (digit - 1) ("0" ^ res)
  else
    res

let reg_to_binary reg =
  int_to_binary (int_of_string (String.sub reg 1 (String.length reg - 1))) 5 ""

let int_to_minus_binary int digit =
  int_to_binary ((int_of_float (2. ** (float_of_int digit))) - int) digit ""

let br_to_binary b = match b with
  | "bgt" -> "0100000101000000"

let byte_to_int s =
  128 * (int_of_char s.[0] - 48) +
  64 * (int_of_char s.[1] - 48) +
  32 * (int_of_char s.[2] - 48) +
  16 * (int_of_char s.[3] - 48) +
  8 * (int_of_char s.[4] - 48) +
  4 * (int_of_char s.[5] - 48) +
  2 * (int_of_char s.[6] - 48) +
  (int_of_char s.[7] - 48)

let rec write_byte bc str=
  if str <> "" then
   (output_byte bc (byte_to_int (Str.string_before str 8));
    write_byte bc (Str.string_after str 8))

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
      Printf.fprintf oc "\tli\t%s, %d\n" (reg x) i;
      file := !file ^ Printf.sprintf "001110%s00000%s\n" (reg_to_binary (reg x)) (int_to_binary i 16 "");
      address := !address + 4
  | (NonTail(x), Li(i)) ->
      let n = i lsr 16 in
      let m = i lxor (n lsl 16) in
      let r = reg x in
	Printf.fprintf oc "\tlis\t%s, %d\n" r n;
	Printf.fprintf oc "\tori\t%s, %s, %d\n" r r m;
	file := !file ^ Printf.sprintf "001110%s00000%s\n" (reg_to_binary r) (int_to_binary n 16 "");
	file := !file ^ Printf.sprintf "011001%s%s%s\n" (reg_to_binary r) (reg_to_binary r) (int_to_binary m 16 "");
	address := !address + 8
  | (NonTail(x), FLi(Id.L(l))) ->
      let s = load_label reg_tmp l in
      Printf.fprintf oc "%s\tlf\t%s, 0(%s)\n" s (reg x) reg_tmp;
      file := !file ^ Printf.sprintf "110010%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary reg_tmp);
      address := !address + 4
  | (NonTail(x), SetL(Id.L(y))) ->
      let s = load_label x y in
      Printf.fprintf oc "%s" s;
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) ->
     Printf.fprintf oc "\tmr\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011111%s%s%s01101111000\n" (reg_to_binary (reg y)) (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4
  | (NonTail(x), Neg(y)) ->
     Printf.fprintf oc "\tneg\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), Add(y, V(z))) ->
      Printf.fprintf oc "\tadd\t%s, %s, %s\n" (reg x) (reg y) (reg z);
      file := !file ^ Printf.sprintf "011111%s%s%s01000010100\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
      address := !address + 4
  | (NonTail(x), Add(y, C(z))) ->
     Printf.fprintf oc "\taddi\t%s, %s, %d\n" (reg x) (reg y) z;
     file := !file ^ Printf.sprintf "001110%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (int_to_binary z 16 "");
     address := !address + 4
  | (NonTail(x), Sub(y, V(z))) ->
     file := !file ^ Printf.sprintf "\tsub\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Sub(y, C(z))) ->
     Printf.fprintf oc "\tsubi\t%s, %s, %d\n" (reg x) (reg y) z;
     file := !file ^ Printf.sprintf "001110%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (int_to_minus_binary z 16);
     address := !address + 4
  | (NonTail(x), Slw(y, V(z))) ->
     Printf.fprintf oc "\tslw\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Slw(y, C(z))) ->
     Printf.fprintf oc "\tslwi\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Lwz(y, V(z))) ->
     Printf.fprintf oc "\tldx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "011111%s%s%s00000101110\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(x), Lwz(y, C(z))) ->
     Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" (reg x) z (reg y);
     file := !file ^ Printf.sprintf "100000%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (int_to_binary z 16 "");
     address := !address + 4
  | (NonTail(_), Stw(x, y, V(z))) ->
     Printf.fprintf oc "\tstx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "011111%s%s%s00100101110\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(_), Stw(x, y, C(z))) ->
     Printf.fprintf oc "\tst\t%s, %d(%s)\n" (reg x) z (reg y);
     file := !file ^ Printf.sprintf "100100%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (int_to_binary z 16 "");
     address := !address + 4
  | (NonTail(x), FMr(y)) when x = y -> ()
  | (NonTail(x), FMr(y)) ->
     Printf.fprintf oc "\tfmr\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "111111%s00000%s00010010000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4
  | (NonTail(x), FNeg(y)) ->
     Printf.fprintf oc "\tfneg\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "111111%s00000%s01000010000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4
  | (NonTail(x), FAdd(y, z)) ->
     Printf.fprintf oc "\tfadd\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "11111%s%s%s00000101010\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(x), FSub(y, z)) ->
     Printf.fprintf oc "\tfsub\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "11111%s%s%s00000101000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(x), FMul(y, z)) ->
     Printf.fprintf oc "\tfmul\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "11111%s%s%s00000110010\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(x), FDiv(y, z)) ->
     Printf.fprintf oc "\tfdiv\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "11111%s%s%s00000100100\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(x), Lfd(y, V(z))) ->
     Printf.fprintf oc "\tlfx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "011111%s%s%s10010101110\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(x), Lfd(y, C(z))) ->
     Printf.fprintf oc "\tlf\t%s, %d(%s)\n" (reg x) z (reg y);
     file := !file ^ Printf.sprintf "110010%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (int_to_binary z 16 "");
     address := !address + 4
  | (NonTail(_), Stfd(x, y, V(z))) ->
     Printf.fprintf oc "\tstfx\t%s, %s, %s\n" (reg x) (reg y) (reg z);
     file := !file ^ Printf.sprintf "011111%s%s%s10100101110\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (reg_to_binary (reg z));
     address := !address + 4
  | (NonTail(_), Stfd(x, y, C(z))) ->
     Printf.fprintf oc "\tstf\t%s, %d(%s)\n" (reg x) z (reg y);
     file := !file ^ Printf.sprintf "110100%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary (reg y)) (int_to_binary z 16 "");
     address := !address + 4
  | (NonTail(_), Comment(s)) ->
     file := !file ^ Printf.sprintf "#\t%s\n" s
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
      when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
        Printf.fprintf oc "\tstw\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
	file := !file ^ Printf.sprintf "100100%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary reg_sp) (int_to_binary (offset y) 16 "");
	address := !address + 4
  | (NonTail(_), Save(x, y))
      when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
	Printf.fprintf oc "\tstf\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
	file := !file ^ Printf.sprintf "110100%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary reg_sp) (int_to_binary (offset y) 16 "");
	address := !address + 4
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
     Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
     file := !file ^ Printf.sprintf "100000%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary reg_sp) (int_to_binary (offset y) 16 "");
     address := !address + 4
  | (NonTail(x), Restore(y)) ->
     assert (List.mem x allfregs);
     Printf.fprintf oc "\tlf\t%s, %d(%s)\n" (reg x) (offset y) reg_sp;
     file := !file ^ Printf.sprintf "110010%s%s%s\n" (reg_to_binary (reg x)) (reg_to_binary reg_sp) (int_to_binary (offset y) 16 "");
     address := !address + 4
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Comment _ | Save _ as exp)) ->
     g' oc (NonTail(Id.gentmp Type.Unit), exp);
     Printf.fprintf oc "\tblr\n";
     file := !file ^ Printf.sprintf "01001100000000000000000000000000\n";
     address := !address + 4
  | (Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | Slw _ |
            Lwz _ as exp)) ->
     g' oc (NonTail(regs.(0)), exp);
     Printf.fprintf oc "\tblr\n";
     file := !file ^ Printf.sprintf "01001100000000000000000000000000\n";
     address := !address + 4
  | (Tail, (FLi _ | FMr _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ |
            Lfd _ as exp)) ->
      g' oc (NonTail(fregs.(0)), exp);
      Printf.fprintf oc "\tblr\n";
      file := !file ^ Printf.sprintf "01001100000000000000000000000000\n";
      address := !address + 4
  | (Tail, (Restore(x) as exp)) ->
      (match locate x with
	 | [i] -> g' oc (NonTail(regs.(0)), exp)
	 | [i; j] when (i + 1 = j) -> g' oc (NonTail(fregs.(0)), exp)
	 | _ -> assert false);
      Printf.fprintf oc "\tblr\n";
      file := !file ^ Printf.sprintf "01001100000000000000000000000000\n";
      address := !address + 4
  | (Tail, IfEq(x, V(y), e1, e2)) ->
     Printf.fprintf oc "\tcmp\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_tail_if oc e1 e2 "beq" "bne"
  | (Tail, IfEq(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tcmpi\t%s, %d\n" (reg x) y;
     file := !file ^ Printf.sprintf "001011%s00000%s\n" (reg_to_binary (reg x)) (int_to_binary y 16 "");
     address := !address + 4;
     g'_tail_if oc e1 e2 "beq" "bne"
  | (Tail, IfLE(x, V(y), e1, e2)) ->
     Printf.fprintf oc "\tcmp\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_tail_if oc e1 e2 "ble" "bgt"
  | (Tail, IfLE(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tcmpi\t%s, %d\n" (reg x) y;
     file := !file ^ Printf.sprintf "001011%s00000%s\n" (reg_to_binary (reg x)) (int_to_binary y 16 "");
     address := !address + 4;
     g'_tail_if oc e1 e2 "ble" "bgt"
  | (Tail, IfGE(x, V(y), e1, e2)) ->
     Printf.fprintf oc "\tcmp\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_tail_if oc e1 e2 "bge" "blt"
  | (Tail, IfGE(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tcmpi\t%s, %d\n" (reg x) y;
     file := !file ^ Printf.sprintf "001011%s00000%s\n" (reg_to_binary (reg x)) (int_to_binary y 16 "");
     address := !address + 4;
     g'_tail_if oc e1 e2 "bge" "blt"
  | (Tail, IfFEq(x, y, e1, e2)) ->
     Printf.fprintf oc "\tfcmpu\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_tail_if oc e1 e2 "beq" "bne"
  | (Tail, IfFLE(x, y, e1, e2)) ->
     Printf.fprintf oc "\tfcmpu\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_tail_if oc e1 e2 "ble" "bgt"
  | (NonTail(z), IfEq(x, V(y), e1, e2)) ->
     Printf.fprintf oc "\tcmp\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne"
  | (NonTail(z), IfEq(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tcmpi\t%s, %d\n" (reg x) y;
     file := !file ^ Printf.sprintf "001011%s00000%s\n" (reg_to_binary (reg x)) (int_to_binary y 16 "");
     address := !address + 4;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne"
  | (NonTail(z), IfLE(x, V(y), e1, e2)) ->
     Printf.fprintf oc "\tcmp\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt"
  | (NonTail(z), IfLE(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tcmpi\t%s, %d\n" (reg x) y;
     file := !file ^ Printf.sprintf "001011%s00000%s\n" (reg_to_binary (reg x)) (int_to_binary y 16 "");
     g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt"
  | (NonTail(z), IfGE(x, V(y), e1, e2)) ->
     Printf.fprintf oc "\tcmp\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt"
  | (NonTail(z), IfGE(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tcmpi\t%s, %d\n" (reg x) y;
     file := !file ^ Printf.sprintf "001011%s00000%s\n" (reg_to_binary (reg x)) (int_to_binary y 16 "");
     address := !address + 4;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "bge" "blt"
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
     Printf.fprintf oc "\tfcmpu\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne"
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
     Printf.fprintf oc "\tfcmpu\t%s, %s\n" (reg x) (reg y);
     file := !file ^ Printf.sprintf "011110%s%s0000000000000000\n" (reg_to_binary (reg x)) (reg_to_binary (reg y));
     address := !address + 4;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt"
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
     g'_args oc [(x, reg_cl)] ys zs;
     Printf.fprintf oc "\tlwz\t%s, 0(%s)\n" (reg reg_sw) (reg reg_cl);
     file := !file ^ Printf.sprintf "100000%s%s0000000000000000\n" (reg_to_binary (reg reg_sw)) (reg_to_binary (reg reg_cl));
     Printf.fprintf oc "\tmtctr\t%s\n\tbctr\n" (reg reg_sw);
     file := !file ^ Printf.sprintf "011011%s000000000001110100110\n" (reg_to_binary (reg reg_sw));
     file := !file ^ Printf.sprintf "01001100000000000000000000000000\n";
     address := !address + 12;
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
     g'_args oc [] ys zs;
     Printf.fprintf oc "\tb\t%s\n" x;
     file := !file ^ Printf.sprintf "0100100000000000%s\n" (int_to_binary (Hashtbl.find address_list x) 16 "");
     address := !address + 4
  | (NonTail(a), CallCls(x, ys, zs)) ->
     Printf.fprintf oc "\tmflr\t%s\n" reg_tmp;
     file := !file ^ Printf.sprintf "011111%s000000000001010100110\n" (reg_to_binary reg_tmp);
     address := !address + 4;
     g'_args oc [(x, reg_cl)] ys zs;
     let ss = stacksize () in
       Printf.fprintf oc "\tst\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
       file := !file ^ Printf.sprintf "100100%s%s%s\n" (reg_to_binary reg_tmp) (reg_to_binary reg_sp) (int_to_binary (ss - 4) 16 "");
       Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
       file := !file ^ Printf.sprintf "001110%s%s%s\n" (reg_to_binary reg_sp) (reg_to_binary reg_sp) (int_to_binary ss 16 "");
       Printf.fprintf oc "\tld\t%s, 0(%s)\n" reg_tmp (reg reg_cl);
       file := !file ^ Printf.sprintf "100000%s%s0000000000000000\n" (reg_to_binary reg_tmp) (reg_to_binary reg_sp);
       Printf.fprintf oc "\tmtctr\t%s\n" reg_tmp;
       file := !file ^ Printf.sprintf "011011%s000000000001110100110\n" (reg_to_binary reg_tmp);
       Printf.fprintf oc "\tbctrl\n";
       file := !file ^ Printf.sprintf "01001100000000000000000000000000\n";
       Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
       file := !file ^ Printf.sprintf "001110%s%s%s\n" (reg_to_binary reg_sp) (reg_to_binary reg_sp) (int_to_minus_binary ss 16);
       Printf.fprintf oc "\tld\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
       file := !file ^ Printf.sprintf "100000%s%s%s\n" (reg_to_binary reg_tmp) (reg_to_binary reg_sp) (int_to_binary (ss - 4) 16 "");
       address := !address + 28;
       (if List.mem a allregs && a <> regs.(0) then
	 (Printf.fprintf oc "\tmr\t%s, %s\n" (reg a) (reg regs.(0));
	  file := !file ^ Printf.sprintf "011111%s%s%s01101111000\n" (reg_to_binary (reg regs.(0))) (reg_to_binary (reg a)) (reg_to_binary (reg regs.(0)));
	  address := !address + 4)
	else if List.mem a allfregs && a <> fregs.(0) then
	 (Printf.fprintf oc "\tfmr\t%s, %s\n" (reg a) (reg fregs.(0));
	  file := !file ^ Printf.sprintf "111111%s00000%s00010010000\n" (reg_to_binary (reg a)) (reg_to_binary (reg fregs.(0)));
	  address := !address + 4));
       Printf.fprintf oc "\tmtlr\t%s\n" reg_tmp;
       file := !file ^ Printf.sprintf "011111%s000000000001110100110\n" (reg_to_binary reg_tmp);
       address := !address + 4
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) ->
      Printf.fprintf oc "\tmflr\t%s\n" reg_tmp;
      file := !file ^ Printf.sprintf "011111%s000000000001010100110\n" (reg_to_binary reg_tmp);
      address := !address + 4;
      g'_args oc [] ys zs;
      let ss = stacksize () in
	Printf.fprintf oc "\tst\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
	file := !file ^ Printf.sprintf "100100%s%s%s\n" (reg_to_binary reg_tmp) (reg_to_binary reg_sp) (int_to_binary (ss - 4) 16 "");
	Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
	file := !file ^ Printf.sprintf "001110%s%s%s\n" (reg_to_binary reg_sp) (reg_to_binary reg_sp) (int_to_binary ss 16 "");
	Printf.fprintf oc "\tbl\t%d\n" (Hashtbl.find address_list x);
	file := !file ^ Printf.sprintf "0100101000000000%s\n" (int_to_binary (Hashtbl.find address_list x) 16 "");
	Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
	file := !file ^ Printf.sprintf "001110%s%s%s\n" (reg_to_binary reg_sp) (reg_to_binary reg_sp) (int_to_minus_binary ss 16);
	Printf.fprintf oc "\tld\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
	file := !file ^ Printf.sprintf "100000%s%s%s\n" (reg_to_binary reg_tmp) (reg_to_binary reg_sp) (int_to_binary (ss - 4) 16 "");
	address := !address + 20;
	(if List.mem a allregs && a <> regs.(0) then
	  (Printf.fprintf oc "\tmr\t%s, %s\n" (reg a) (reg regs.(0));
	   file := !file ^ Printf.sprintf "011111%s%s%s01101111000\n" (reg_to_binary (reg regs.(0))) (reg_to_binary (reg a)) (reg_to_binary (reg regs.(0)));
	   address := !address + 4)
	 else if List.mem a allfregs && a <> fregs.(0) then
	  (Printf.fprintf oc "\tfmr\t%s, %s\n" (reg a) (reg fregs.(0));
	   file := !file ^ Printf.sprintf "111111%s00000%s00010010000\n" (reg_to_binary (reg a)) (reg_to_binary (reg fregs.(0)));
	   address := !address + 4));
	Printf.fprintf oc "\tmtlr\t%s\n" reg_tmp;
	file := !file ^ Printf.sprintf "011111%s000000000001110100110\n" (reg_to_binary reg_tmp);
	address := !address + 4
and g'_tail_if oc e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
    Printf.fprintf oc "\t%s\tcr7, %s\n" bn b_else;
    file := !file ^ Printf.sprintf "%s%s\n" (br_to_binary bn) b_else;
    address := !address + 4;
    let stackset_back = !stackset in
      g oc (Tail, e1);
      Printf.fprintf oc "%s:\n" b_else;
      file := Str.global_replace (Str.regexp b_else) (int_to_binary !address 16 "") !file;
      stackset := stackset_back;
      g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b bn =
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
    Printf.fprintf oc "\t%s\tcr7, %s\n" bn b_else;
    file := !file ^ Printf.sprintf "%s%s\n" (br_to_binary bn) b_else;
    address := !address + 4;
    let stackset_back = !stackset in
      g oc (dest, e1);
      let stackset1 = !stackset in
        Printf.fprintf oc "\tb\t%s\n" b_cont;
	file := !file ^ Printf.sprintf "0100100000000000%s\n" b_cont;
	address := !address + 4;
	Printf.fprintf oc "%s:\n" b_else;
	file := Str.global_replace (Str.regexp b_else) (int_to_binary !address 16 "") !file;
	stackset := stackset_back;
	g oc (dest, e2);
	Printf.fprintf oc "%s:\n" b_cont;
	file := Str.global_replace (Str.regexp b_cont) (int_to_binary !address 16 "") !file;
	let stackset2 = !stackset in
	  stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys zs =
  let (i, yrs) =
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl) ys in
    List.iter
      (fun (y, r) -> (Printf.fprintf oc "\tmr\t%s, %s\n" (reg r) (reg y);
		      file := !file ^ Printf.sprintf "011111%s%s%s01101111000\n" (reg_to_binary (reg y)) (reg_to_binary (reg r)) (reg_to_binary (reg y));
		      address := !address + 4))
      (shuffle reg_sw yrs);
    let (d, zfrs) =
      List.fold_left
	(fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
	(0, []) zs in
      List.iter
        (fun (z, fr) -> (Printf.fprintf oc "\tfmr\t%s, %s\n" (reg fr) (reg z);
			 file := !file ^ Printf.sprintf "111111%s00000%s00010010000\n" (reg_to_binary (reg fr)) (reg_to_binary (reg z));
			 address := !address + 4))
	(shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;
  stackset := S.empty;
  stackmap := [];
  Hashtbl.add address_list x !address;
  g oc (Tail, e)

(* let f oc (Prog(data, fundefs, e)) = *)
let f oc bc p =
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
  Printf.fprintf oc "# main entry point\n";
  g oc (NonTail("_R_0"), e);
  print_string ("all " ^ (string_of_int !address) ^ " lines in total\n");
  file := !file ^ Printf.sprintf "11111111111111111111111111111111\n";
  write_byte bc (Str.global_replace (Str.regexp "\n") "" !file)
