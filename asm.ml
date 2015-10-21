(* PowerPC assembly with a few virtual instructions *)
open Id

type id_or_imm = V of Id.t | C of int
type t = (* 命令の列 *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Li of int
  | FLi of Id.l
  | SetL of Id.l
  | Mr of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Slw of Id.t * id_or_imm
  | Lwz of Id.t * id_or_imm
  | Stw of Id.t * Id.t * id_or_imm
  | FMr of Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 *)
type prog = Prog of (Id.l * float) list * fundef list * t

(* shorthand of Let for float *)
(* fletd : Id.t * exp * t -> t *)
let fletd (x, e1, e2) = Let ((x, Type.Float), e1, e2)
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = [| "%r2"; "%r5"; "%r6"; "%r7"; "%r8"; "%r9"; "%r10";
  "%r11"; "%r12"; "%r13"; "%r14"; "%r15"; "%r16"; "%r17"; "%r18";
  "%r19"; "%r20"; "%r21"; "%r22"; "%r23"; "%r24"; "%r25"; "%r26";
  "%r27"; "%r28"; "%r29"; "%r30" |]
(* let regs = Array.init 27 (fun i -> Printf.sprintf "_R_%d" i) *)
let fregs = Array.init 32 (fun i -> Printf.sprintf "%%f%d" i)
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let reg_cl = regs.(Array.length regs - 1) (* closure address *)
let reg_sw = regs.(Array.length regs - 2) (* temporary for swap *)
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
let reg_hp = "%r4"
let reg_sp = "r3"
let reg_tmp = "r31"

(* is_reg : Id.t -> bool *)
let is_reg x = x.[0] = '%'

(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) *)
(* fv_id_or_imm : id_or_imm -> Id.t list *)
let fv_id_or_imm = function V (x) -> [x] | _ -> []
(* fv_exp : Id.t list -> t -> S.t list *)
let rec fv_exp = function
  | Nop | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | Neg (x) | FMr (x) | FNeg (x) | Save (x, _) -> [x]
  | Add (x, y') | Sub (x, y') | Slw (x, y') | Lfd (x, y') | Lwz (x, y') ->
      x :: fv_id_or_imm y'
  | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) ->
      [x; y]
  | Stw (x, y, z') | Stfd (x, y, z') -> x :: y :: fv_id_or_imm z'
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) ->
      x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv e1 @ fv e2)
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
      x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2)
  | CallCls (x, ys, zs) -> x :: ys @ zs
  | CallDir (_, ys, zs) -> ys @ zs
and fv = function
  | Ans (exp) -> fv_exp exp
  | Let ((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)

(* fv : t -> Id.t list *)
let fv e = remove_and_uniq S.empty (fv e)

(* concat : t -> Id.t * Type.t -> t -> t *)
let rec concat e1 xt e2 = match e1 with
  | Ans (exp) -> Let (xt, exp, e2)
  | Let (yt, exp, e1') -> Let (yt, exp, concat e1' xt e2)

(* align : int -> int *)
let align i = if i mod 8 = 0 then i else i + 4

let print_prog_data (L(l), f) =
  print_string ("\t" ^ l ^ "\t");
  print_float f;
  print_string "\n"

let rec print_prog_datas datas = match datas with
  | [] -> ()
  | y::ys -> print_prog_data y; print_prog_datas ys

let rec args_to_string string args = match args with
  | [] -> string
  | y::ys -> args_to_string (string ^ y ^ " ") ys

let id_or_imm_to_string i = match i with
  | V (id) -> id
  | C (int) -> string_of_int int

let rec print_asm_t indent t = match t with
  | Ans (exp) -> print_string (indent ^ "Ans\n"); print_asm_exp indent exp
  | Let ((x, xt), exp, t) ->
     print_string (indent ^ "LET " ^ x ^ " : " ^ (Type.type_to_string xt) ^ " =\n");
     print_asm_exp (indent ^ "  ") exp;
     print_asm_t indent t;
and print_asm_exp indent exp = match exp with
  | Nop -> print_string (indent ^ "NOP\n")
  | Li (int) -> print_string (indent ^ "Li " ^ (string_of_int int) ^ "\n")
  | FLi (L(l)) -> print_string (indent ^ "FLi " ^ l ^ "\n")
  | SetL (L(l)) -> print_string (indent ^ "SetL" ^ l ^ "\n")
  | Mr (t) -> print_string (indent ^ "Mr " ^ t ^ "\n")
  | Neg (t) -> print_string (indent ^ "Neg " ^ t ^ "\n")
  | Add (t, i) -> print_string (indent ^ "Add " ^ t ^ " " ^ (id_or_imm_to_string i) ^ "\n")
  | Sub (t, i) -> print_string (indent ^ "Sub " ^ t ^ " " ^ (id_or_imm_to_string i) ^ "\n")
  | Slw (t, i) -> print_string (indent ^ "Slw " ^ t ^ " " ^ (id_or_imm_to_string i) ^ "\n")
  | Lwz (t, i) -> print_string (indent ^ "Lwz " ^ t ^ " " ^ (id_or_imm_to_string i) ^ "\n")
  | Stw (t1, t2, i) -> print_string (indent ^ "Stw " ^ t1 ^ " " ^ t2 ^ " " ^ (id_or_imm_to_string i) ^ "\n")
  | FMr (t) -> print_string (indent ^ "FMr " ^ t ^ "\n")
  | FNeg (t) -> print_string (indent ^ "FNeg " ^ t ^ "\n")
  | FAdd (t1, t2) -> print_string (indent ^ "FAdd " ^ t1 ^ " " ^ t2 ^ "\n")
  | FSub (t1, t2) -> print_string (indent ^ "FSub " ^ t1 ^ " " ^ t2 ^ "\n")
  | FMul (t1, t2) -> print_string (indent ^ "FMul " ^ t1 ^ " " ^ t2 ^ "\n")
  | FDiv (t1, t2) -> print_string (indent ^ "FDiv " ^ t1 ^ " " ^ t2 ^ "\n")
  | Lfd (t, i) -> print_string (indent ^ "Lfd " ^ t ^ " " ^ (id_or_imm_to_string i) ^ "\n")
  | Stfd (t1, t2, i) -> print_string (indent ^ "Stfd " ^ t1 ^ " " ^ t2 ^ " " ^ (id_or_imm_to_string i) ^ "\n")
  | Comment (s) -> print_string (indent ^ "Comment " ^ s ^ "\n")
  | IfEq (i, id, t1, t2) ->
     print_string (indent ^ "IfEq " ^ i ^ " " ^ (id_or_imm_to_string id) ^ " Then\n");
     print_asm_t (indent ^ "  ") t1;
     print_string (indent ^ "Else\n");
     print_asm_t (indent ^ "  ") t2
  | IfLE (i, id, t1, t2) ->
     print_string (indent ^ "IfLE " ^ i ^ " " ^ (id_or_imm_to_string id) ^ " Then\n");
     print_asm_t (indent ^ "  ") t1;
     print_string (indent ^ "Else\n");
     print_asm_t (indent ^ "  ") t2
  | IfGE (i, id, t1, t2) ->
     print_string (indent ^ "IfGE " ^ i ^ " " ^ (id_or_imm_to_string id) ^ " Then\n");
     print_asm_t (indent ^ "  ") t1;
     print_string (indent ^ "Else\n");
     print_asm_t (indent ^ "  ") t2
  | IfFEq (i1, i2, t1, t2) ->
     print_string (indent ^ "IfFEq " ^ i1 ^ " " ^ i2 ^ " Then\n");
     print_asm_t (indent ^ "  ") t1;
     print_string (indent ^ "Else\n");
     print_asm_t (indent ^ "  ") t2
  | IfFLE (i1, i2, t1, t2) ->
     print_string (indent ^ "IfFLE " ^ i1 ^ " " ^ i2 ^ " Then\n");
     print_asm_t (indent ^ "  ") t1;
     print_string (indent ^ "Else\n");
     print_asm_t (indent ^ "  ") t2
  | CallCls (i, is1, is2) ->
     print_string (indent ^ "CallCls\n");
     print_string (indent ^ "  1st param : " ^ i ^ "\n");
     print_string (indent ^ "  2nd param : " ^ (args_to_string "" is1) ^ "\n");
     print_string (indent ^ "  3rd param : " ^ (args_to_string "" is2) ^ "\n")
  | CallDir (L(l), is1, is2) ->
     print_string (indent ^ "CallDir\n");
     print_string (indent ^ "  1st param : " ^ l ^ "\n");
     print_string (indent ^ "  2nd param : " ^ (args_to_string "" is1) ^ "\n");
     print_string (indent ^ "  3rd param : " ^ (args_to_string "" is2) ^ "\n")
  | Save (t1, t2) -> print_string (indent ^ "Save " ^ t1 ^ " " ^ t2 ^ "\n")
  | Restore (t) -> print_string (indent ^ "Restore " ^ t ^ "\n")

let print_prog_fundef { name = L(n); args = args; fargs = fargs; body = body; ret = ret } =
  print_string ("\tFundef " ^ n ^ "\n");
  print_string ("\tArgs " ^ (args_to_string "" args) ^ "\n");
  print_string ("\tFargs " ^ (args_to_string "" fargs) ^ "\n");
  print_string "\tBody\n";
  print_asm_t "\t" body;
  print_string ("\tRet " ^ (Type.type_to_string ret) ^ "\n")

let rec print_prog_fundefs fundefs = match fundefs with
  | [] -> ()
  | y::ys -> print_prog_fundef y; print_prog_fundefs ys

(* show_asm_prog : string -> prog -> unit *)
let show_asm_prog indent p =
  let Prog(datas, fundefs, e) = p in
  print_string "=======================\n";
  print_string "\tAsm.Prog\n";
  print_string "=======================\n";
  print_string "\tshowing asm prog structure...\n";
  print_string "\tstarted printing datas...\n";
  print_prog_datas datas;
  print_string "\tstarted printing fundefs...\n";
  print_prog_fundefs fundefs;
  print_string "\tstarted printing asm t...\n";
  print_asm_t (indent ^ "\t") e;
  print_string "=======================\n"
