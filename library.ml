(* #create_array *)
(* #create_float_array *)
(* #int_of_float *)
(* #float_of_int *)

(* #print_newline *)
(* putchar *)
(* #print_int *)
(* printf *)
(* #print_byte *)
(* #prerr_int *)
(* fprintf *)
(* #prerr_byte *)
(* fputc *)
(* #prerr_float *)
(* #read_int *)
(* #read_float *)

(* fabs *)
let rec fabs x =
  if x > 0.0 then x else (0.0-.x)
in
(* #sqrt *)
let rec sqrt_sub x a =
  let xn = (x +. a/.x) *. 0.5 in
  if ((fabs (xn*.xn -. a)) < 0.00001) then
    xn
  else
    (sqrt_sub xn a)
in
let rec sqrt a = sqrt_sub a a

(* #floor *)
(*let rec floor x =
  if x < 0.0 then (truncate (x -. 1.0)) else (truncate x)*)

(* truncate *)
(*let rec truncate x = int_of_float x*)
in

(* #cos *)
let rec cos x =
  let x2 = x*.x in
  let x4 = x2*.x2 in
  1.0 -. x2/.2.0
      +. x4/.24.0
      -. x4*.x2/.720.0
      +. x4*.x4/.40320.0

in
(* #sin *)
let rec sin x =
  let x2 = x*.x in
  let x3 = x2*.x in
  let x5 = x3*.x2 in
  let x7 = x5*.x2 in
  x -. x3/.6.0
    +. x5/.120.0
    -. x7/.5040.0
    +. x7*.x2/.362880.0
in

(* #atan *)(* only around 0 *)
let rec atan x =
  let x2 = x*.x in
  let x3 = x2*.x in
  let x5 = x3*.x2 in
  let x7 = x5*.x2 in
  x -. x3/.3.0
    +. x5/.5.0
    -. x7/.7.0
    +. x7*.x2/.9.0
in
0
