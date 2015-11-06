let n = create_array 5 20 in
let m = create_array 3 (float_of_int n.(1)) in
let rec fib n =
  if n <= 1.0 then n else
  fib (n -. 1.0) +. fib (n -. 2.0) in
let _ = fib m.(0) in
0
