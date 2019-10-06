type ('a, 's) t = 's -> 'a * 's

let run ma = ma
let return x s = (x, s)

let map f ma s =
  let x, s' = ma s in
  (f x, s')

let bind ma f s =
  let x, s' = ma s in
  f x s'

let and_then ma mb = bind ma (fun () -> mb)
let get s = (s, s)
let set s _ = ((), s)
let modify f s = ((), f s)
