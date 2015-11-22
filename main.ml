let limit = ref 1000

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf outchan binchan datachan zerochan l = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := M.empty;
  Emit.f outchan binchan datachan zerochan
    (RegAlloc.f
      (Simm.f
	 (Virtual.f
	    (Closure.f
	       (iter !limit
		     (Alpha.f
			(KNormal.f
			   (Typing.f
			      (Parser.exp Lexer.token l)))))))))

let string s = lexbuf stdout stdout stdout stdout (Lexing.from_string s) (* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let deal_with_file_name f =
  if (String.sub f (String.length f - 3) 3) = ".ml" then String.sub f 0 (String.length f - 3) else f

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let fname = deal_with_file_name f in
  let inchan = open_in (fname ^ ".ml") in
  let outchan = open_out ("result/" ^ fname ^ ".s") in
  let binchan = open_out ("result/" ^ fname ^ ".bin") in
  let datachan = open_out ("result/" ^ fname ^ ".data") in
  let zerochan = open_out ("result/" ^ fname ^ ".zero") in
  try
    let libchan = open_in ("lib/lib.ml") in
    let liblength = in_channel_length libchan in
    let libstring = String.create liblength in
    really_input libchan libstring 0 liblength;
    close_in libchan;
    let inlength = in_channel_length inchan in
    let instring = String.create inlength in
    really_input inchan instring 0 inlength;
    lexbuf outchan binchan datachan zerochan (Lexing.from_string (libstring ^ instring));
    close_in inchan;
    close_out outchan;
    close_out binchan;
    close_out datachan;
    close_out zerochan;
  with e -> (close_in inchan; close_out outchan; close_out binchan; close_out datachan; close_out zerochan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files
