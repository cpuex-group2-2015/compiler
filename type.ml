type t = (* MinCamlの型を表現するデータ型 (caml2html: type_t) *)
  | Unit
  | Bool
  | Int
  | Float
  | Fun of t list * t (* arguments are uncurried *)
  | Tuple of t list
  | Array of t
  | Var of t option ref

let gentyp () = Var(ref None) (* 新しい型変数を作る *)

let rec type_to_string t =
  match t with
  | Unit -> "Unit"
  | Bool -> "Bool"
  | Int -> "Int"
  | Float -> "Float"
  | Fun(ts, t) -> " Func of " ^ (types_to_string "" ts) ^ " to " ^ (type_to_string t)
  | Tuple(ts) -> "Tuple of " ^ (types_to_string "" ts)
  | Array(at) -> "Array of " ^ (type_to_string at)
  | Var(sthref) ->
     let sth = !sthref in
     match sth with
     | Some(s) -> "Var of " ^ (type_to_string s)
     | None -> "Var of None"
and types_to_string string ts =
  match ts with
  | [] -> string
  | y::ys -> types_to_string (string ^ (type_to_string y) ^ " ") ys
