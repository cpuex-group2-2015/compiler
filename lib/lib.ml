let rec fless fa fb = fa < fb in
let rec fispos f = f > 0.0 in
let rec fisneg f = f < 0.0 in
let rec fiszero f = (f = 0.0) in
let rec fhalf f = f *. 0.5 in
let rec fsqr f = f *. f in
let rec fneg f = 0.0 -. f in

let rec divide10 i res ten =
  if i < (ten + 10) then
    (res, (i - ten))
  else
    divide10 i (res + 1) (ten + 10)
in

let rec print_int i =
  if i < 10 then
    print_char (48 + i)
  else
   (let (d, m) = divide10 i 1 10 in
    print_int d;
    print_char (48 + m))
in

let rec int_of_float f =
  let i = int_of_float_sub f in
  if f < 0.0 then -i else i
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
  if ((fabs (a -. x *. x)) < 0.00001) then
    x
  else
    let xn = (x +. a/.x) *. 0.5 in
    if ((x -. xn) < 0.00001) then x else (sqrt_sub xn a)
in

let rec sqrt a = sqrt_sub a a in

let rec truncate x = int_of_float x in

let rec floor x = if x > 0.0 then (float_of_int (truncate x)) else (float_of_int (truncate (x -. 1.0))) in

let rec cos x =
  let x2 = x*.x in
  (((x2/.40320.0 -. 1.0/.720.0)*.x2 +. 1.0/.24.0)*.x2 -. 0.5)*.x2 +. 1.0
in

let rec sin x =
  let x2 = x*.x in
  ((((x2/.362880.0 -. 1.0/.5040.0)*.x2 +. 1.0/.120.0)*.x2 -. 1.0/.6.0)*.x2 +. 1.0)*.x
in

let rec atan_tail x =
  (if (x >= 10.0) then 1.57079633
   else
     (let y = 1.0/.x in
      let y2 = y *. y in
      0.0 -. (((((((((((-0.01183641) *. y2
                      +. 0.03130684) *. y2
                      -. 0.04709780) *. y2
                      +. 0.05755726) *. y2
                      -. 0.06646850) *. y2
                      +. 0.07690189) *. y2
                      -. 0.09090757) *. y2
                      +. 0.11111104) *. y2
                      -. 0.14285714) *. y2
                      +. 0.20000000) *. y2
                      -. 0.33333333) *. y2 *. y -. y +. 1.57079633
     )
  ) in

let rec atan_i0 x =
  let x2 = x *. x in
  (((((((((((0.01008980 *. x2
          -. 0.02739990) *. x2
          +. 0.04184614) *. x2
          -. 0.05121468) *. x2
          +. 0.05858217) *. x2
          -. 0.06663806) *. x2
          +. 0.07692074) *. x2
          -. 0.09090896) *. x2
          +. 0.11111111) *. x2
          -. 0.14285714) *. x2
          +. 0.20000000) *. x2
          -. 0.33333333) *. x2 *. x +. x in
let rec atan_i1 x =
  let y = x -. 0.625 in
  (((((((((((0.00416493 *. y
           -. 0.01442113) *. y
           +. 0.01236134) *. y
           +. 0.00780079) *. y
           -. 0.03243830) *. y
           +. 0.03238363) *. y
           +. 0.01291956) *. y
           -. 0.08242614) *. y
           +. 0.10184144) *. y
           +. 0.02130401) *. y
           -. 0.32319152) *. y
           +. 0.71910112) *. y +. 0.55859932 in
let rec atan_i2 x =
  let y = x -. 0.875 in
  (((((((((((0.00010931) *. y
          -. 0.00449174) *. y
          +. 0.00845755) *. y
          -. 0.00653209) *. y
          -. 0.00613355) *. y
          +. 0.02789654) *. y
          -. 0.04342140) *. y
          +. 0.02110209) *. y
          +. 0.07853829) *. y
          -. 0.28067977) *. y
          +. 0.56637168) *. y +. 0.71883 in
let rec atan_i3 x =
  let y = x -. 1.16666667 in
  ((((((((((((-0.00037407) *. y
            +. 0.00080981) *. y
            -. 0.00098087) *. y
            +. 0.00021926) *. y
            +. 0.00231784) *. y
            -. 0.00684700) *. y
            +. 0.01134219) *. y
            -. 0.00912499) *. y
            -. 0.01355570) *. y
            +. 0.07808182) *. y
            -. 0.20927336) *. y
            +. 0.42352941) *. y +. 0.862170056 in
let rec atan_i4 x =
  let y = x -. 1.5 in
  (((((((((((0.00003082) *. y
          +. 0.00010416) *. y
          -. 0.00046247) *. y
          +. 0.00112049) *. y
          -. 0.00190991) *. y
          +. 0.00182978) *. y
          +. 0.00210292) *. y
          -. 0.01680613) *. y
          +. 0.05583371) *. y
          -. 0.14201183) *. y
          +. 0.30769231) *. y +. 0.98279372 in
let rec atan_i5 x =
  let y = x -. 1.83333333 in
  ((((((((((0.00006121) *. y
         -. 0.00014509) *. y
         +. 0.00026033) *. y
         -. 0.00028573) *. y
         -. 0.00029136) *. y
         +. 0.00302673) *. y
         -. 0.01196656) *. y
         +. 0.03650334) *. y
         -. 0.09639336) *. y
         +. 0.22929936) *. y +. 1.07144961 in
let rec atan x =
  (if (x < 0.0) then
     (if (x < -1.0) then
	(if (x < - 1.66666667) then
	   (if (x < -2.0) then
	      (fneg (atan_tail (fneg x)))
	    else
	      (fneg (atan_i5 (fneg x))))
	 else
	   (if (x < -1.33333333) then
	      (fneg (atan_i4 (fneg x)))
	    else
	      (fneg (atan_i3 (fneg x)))))
      else
	(if (x < -0.5) then
	   (if (x < -0.75) then
	      (fneg (atan_i2 (fneg x)))
	    else
	      (fneg (atan_i1 (fneg x))))
	 else
	   (if (x < -0.000000014) then
	      (atan_i0 x)
	    else
	      x)))
   else
     (if (x <= 1.0) then
	(if (x <= 0.5) then
	   (if (x <= 0.000000014) then
	      x
	    else
	      (atan_i0 x))
	 else
	   (if (x <= 0.75) then
	      (atan_i1 x)
	    else
	      (atan_i2 x)))
      else
	(if (x <= 1.66666667) then
	   (if (x <= 1.33333333) then
	      (atan_i3 x)
	    else
	      (atan_i4 x))
	 else
	   (if (x <= 2.0) then
	      (atan_i5 x)
	    else
	      (atan_tail x))))) in

