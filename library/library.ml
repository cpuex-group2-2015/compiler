let rec fless fa fb = fa < fb in
let rec fispos f = f > 0.0 in
let rec fisneg f = f < 0.0 in
let rec fiszero f = (x = 0.0) in
let rec fhalf f = f *. 0.5 in
let rec fsqr f = f *. f in
let rec fneg f = -f in

let rec divide10 i res ten =
  if i < (ten + 10) then
    (res, (i - ten))
  else
    divide10 i (res + 1) (ten + 10)
in

let rec print_int i =
  if i < 10 then
    print_char (48+i)
  else
   (let (d, m) = divide10 i 1 10 in
    print_char (48 + d);
    print_int m)
in

let rec int_of_float f =
  let i = int_of_float_sub f in
  if f < 0 then -i else i
in

let rec sign_of_int i = if i < 0 then 1 else 0 in

let rec exp_man_of_int e two i =
  if i < two then
    let s = sign_of_int i in
    float_of_int_sub s (e+126) (i - two/2)
  else
    exp_man_of_int (e+1) (two*2) i
in

let rec float_of_int i = exp_man_of_int 0 1 i in

let rec fabs x =
  if x > 0.0 then x else (0.0 -. x)
in

let rec sqrt_sub x a =
  let xn = (x +. a/.x) *. 0.5 in
  if ((fabs (xn*.xn -. a)) < 0.00001) then
    xn
  else
    (sqrt_sub xn a)
in

let rec sqrt a = sqrt_sub a a in

let rec truncate x = int_of_float x in

let rec floor x =
  if x < 0.0 then (truncate (x -. 1.0)) else (truncate x)
in

let rec cos x =
  let x2 = x*.x in
  let x4 = x2*.x2 in
  1.0 -. x2/.2.0
      +. x4/.24.0
      -. x4*.x2/.720.0
      +. x4*.x4/.40320.0
in

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

(* only around 0 *)
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
