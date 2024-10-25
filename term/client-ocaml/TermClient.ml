open CoqAPI
open TermAPI.Term

(*Eliminate all let bindings*)
let rec elim_let (t: tm) : tm =
  match t with
  | Tlet (t1, b) ->
      let (x, t2) = t_open_bound b in
      sub_t x (elim_let t1) (elim_let t2)
  | Top (o, t1, t2) -> t_op o (elim_let t1) (elim_let t2)
  | _ -> t

(*Create term with capture:
  let x = 1 in
  let y = x + x in
  let x = y + y in
  y
  The correct simplified value is
  4, naive substitution with capture gives 8
  *)
let rec eval (t: tm) : BigInt.t =
  match t with
  | Tconst z -> z
  | Top(Add, t1, t2) -> BigInt.add (eval t1) (eval t2)
  | Top(Mult, t1, t2) -> BigInt.mul (eval t1) (eval t2)
  | _ -> BigInt.zero

let ex : tm =
  let one = t_const BigInt.one in
  let x = create_var "x" in
  let y = create_var "y" in
  t_let (t_add one one) (t_close_bound x 
    (t_let (t_add (t_var x) (t_var x)) (t_close_bound y
      (t_let (t_add (t_var y) (t_var y)) (t_close_bound x
        (t_var y)
      ))
    ))
  )

let () =
print_endline "Term test:";
print_int(BigInt.to_int (eval(elim_let ex))); (*Prints 4*)

