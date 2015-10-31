open Parser
exception Error of Syntax.t * Type.t * Type.t
val extenv : Type.t M.t ref
val f : Syntax.t -> Syntax.t
val show_token : (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit
