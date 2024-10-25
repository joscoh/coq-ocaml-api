type t = Z.t
let zero = Big_int_Z.zero_big_int
let one = Big_int_Z.unit_big_int
let succ = Big_int_Z.succ_big_int
let pred = Big_int_Z.pred_big_int
let add = Big_int_Z.add_big_int
let sub = Big_int_Z.sub_big_int
let mul = Big_int_Z.mult_big_int
let eq = Big_int_Z.eq_big_int
let lt = Big_int_Z.lt_big_int

(*For testing*)
let to_int = Z.to_int