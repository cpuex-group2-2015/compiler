let rec fib n =
  if n <= 1.0 then n else
  fib (n -. 1.0) +. fib (n -. 2.0) in
let _ = fib 20.0 in
()
