Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Logic.Eqdep_dec.
Require Export Coq.Strings.String.

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.
Coercion is_true : bool >-> Sortclass.

Lemma bool_irrelevance: forall (b: bool) (p1 p2: b), p1 = p2.
Proof.
  intros b p1 p2. apply UIP_dec. apply bool_dec.
Defined.