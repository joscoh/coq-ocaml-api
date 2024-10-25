open CoqAPI

type var
type tm_bound

type intop = | Add | Mult

type tm = private
| Tconst of BigInt.t
| Tvar of var
| Top of intop * tm * tm
| Tlet of tm * tm_bound

(*Type safe API*)
val create_var : string -> var
val t_open_bound: tm_bound -> (var * tm)
val t_close_bound: var -> tm -> tm_bound

val t_const : BigInt.t -> tm
val t_var : var -> tm
val t_op: intop -> tm -> tm -> tm
val t_add : tm -> tm -> tm
val t_mult : tm -> tm -> tm
val t_let : tm -> tm_bound -> tm

val tm_traverse : (BigInt.t -> 'a) -> (var -> 'a) ->
    (intop -> tm -> tm -> 'a -> 'a -> 'a) ->
    (tm -> tm_bound -> 'a -> 'a -> 'a) ->
    tm -> 'a


(*sub_t v t1 t2 is t2[t1/v]*)
val sub_t : var -> tm -> tm -> tm