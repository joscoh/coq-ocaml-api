(*The monadic interface*)
From CoqCompat Require CoqBigInt.
From CoqCompat Require Export Common.
From ExtLib Require Export Monads MonadState StateMonad EitherMonad.

(*Generic monads*)
(*We want to lift a (list (m A)) to a m (list A) for a monad m.
  We can do this in 3 ways:
  1. Use typeclasses
  2. Give a generic function that takes in bind and return
  3. Write the same function for each monad
  Unfortunately, the first 2 ways give horrible OCaml code
  full of Object.magic and that can easily not compile
  (we need non-prenex polymorphism).
  So we do the third (for now)
  Of course in OCaml, these all reduce to the identity function*)
Notation listM ret bnd l :=
  (fold_right (fun x acc =>
    bnd (fun h => bnd (fun t => ret (h :: t)) acc) x)
    (ret nil) l).

(*Error Monad*)
(*We make the exception type a record so we can add more
  elements later*)
Record errtype : Type := { errname : string; errargs: Type; errdata : errargs}.

Definition Not_found : errtype := {| errname := "Not_found"; errargs:= unit; errdata := tt|}.
Definition Invalid_argument (s: string) : errtype :=
  {| errname := "Invalid_argument"; errargs := string; errdata := s|}.

Definition errorM (A: Type) : Type := Datatypes.sum errtype A.

Global Instance Monad_errorM : Monad errorM :=
  Monad_either _.
Global Instance Exception_errorM : MonadExc errtype errorM :=
  Exception_either _.
Definition err_ret {A: Type} (x: A) : errorM A := ret x.
Definition err_bnd {A B: Type} (f: A -> errorM B) (x: errorM A) : errorM B := bind x f.
Definition throw : forall {A: Type} (e: errtype), errorM A :=
  fun A e => raise e.
Definition errorM_list {A: Type} (l: list (errorM A)) : errorM (list A) :=
  listM err_ret err_bnd l.
Definition ignore {A: Type} (x: errorM A) : errorM unit :=
  err_bnd (fun _ => err_ret tt) x.
Definition mk_errtype (name: string) {A: Type} (x: A) : errtype :=
  {| errname := name; errargs := A; errdata := x|}.
(*Try/catch mechanism
  NOTE: could make dependent (ret : (errargs e -> A))
  but much harder to extract
  For OCaml, the last argument NEEDs to take in a unit, or
  else the strict semantics mean that it is always thrown
  The first argument is the same if it is a "raise" *)
Definition trywith {A: Type} (x: unit -> errorM A) (e: errtype) 
  (ret: unit -> errorM A) : errorM A :=
  match x tt with
  | inl e1 => if String.eqb (errname e1) (errname e) then
    ret tt else throw e1
  | inr y => err_ret y
  end.

(*State Monad*)
(*The state monad is more complicated because we want to extract
  to mutable references, but we want to do so safely.
  This means that we want to make [runState] opaque, since 
  the OCaml mutable counter has a single defined state.
  Thus, in our state module (State.v), we want a runState 
  implementation that runs the state only on the initial value.
  However, we cannot make runState fully opaque, because we need
  it in State.v. We mark it as UNSAFE to warn the user not to call it.

  In both Coq and OCaml, our exported 
  runState resets the state to the initial state,
  so that one can begin this whole process again.
  *)

Definition st A B := (state A B). (*For extraction*)
Definition st_bind {A B C: Type} (f: B -> st A C) (x: st A B) : st A C :=
  bind x f.
Definition st_ret {A B: Type} (x: B) : st A B := ret x.
Definition st_list {A B: Type} (l: list (st A B)) : st A (list B) := 
  listM st_ret st_bind l.

Definition dep_fst {A B: Type} (x: A * B) : {a : A | a = fst x} :=
  exist _ (fst x) eq_refl.

(*Dependent version of state so we don't forget info -
see use in term/src/TermAPI.v*)
Definition st_bind_dep (A B C: Type) (x: st A B)
  (f: forall (b: B) (s: A) (Heq: b = fst (runState x s)), st A C) : st A C :=
  mkState 
  (fun (s: A) =>
    runState (f (proj1_sig (dep_fst (runState x s))) s 
      (proj2_sig (dep_fst (runState x s))))
      (snd (runState x s))).

(*ExceptT errtype (state A) monad (error + state)*)

(*We need this to be a definition for extraction.
  We need the typeclass instances because Coq cannot infer
  them otherwise. *)
Definition errState A B := (eitherT errtype (st A) B).
Global Instance Monad_errState A: Monad (errState A) := 
  Monad_eitherT _ (Monad_state _). 
Global Instance MonadT_errorHashconsT K: 
  MonadT (errState K) (st K) := 
  MonadT_eitherT _ (Monad_state _). 
Global Instance MonadState_errorHashconsT K: 
  MonadState K (errState K):= MonadState_eitherT _ (Monad_state _) (MonadState_state _).
Global Instance Exception_errorHashconsT K : 
  MonadExc errtype (errState K) :=
  Exception_eitherT _ (Monad_state _).
Definition errst_lift1 {A B} (s1: st A B) : errState A B :=
  lift s1.
Definition errst_lift2 {A B} (e: errorM B) : errState A B :=
  match e with
  | inl e => raise e
  | inr t => ret t
  end.

(*For extraction*)
Definition errst_bind {A B C : Type} (f: B -> errState A C) (x: errState A B) : errState A C :=
  bind x f.
Definition errst_ret {A B: Type} (x: B) : errState A B := ret x.
Definition errst_list {K A: Type} (l: list (errState K A)) :
  errState K (list A) :=
  listM errst_ret errst_bind l.

(*Try/catch - should reduce duplication*)
Definition errst_trywith {St A B: Type} (x: unit -> errState St A) (e: errtype) 
  (ret: unit -> errState St A) : errState St A :=
  catch (x tt) (fun e1 => if String.eqb (errname e1) (errname e) then ret tt else errst_lift2 (throw e1)).

(*We need different notations for each monad.
  If we use a single notation with typeclasses, the
  resulting OCaml code uses lots of Obj.magic*)
Declare Scope state_scope.
Delimit Scope state_scope with state.
Declare Scope err_scope.
Delimit Scope err_scope with err.
Declare Scope errst_scope.
Delimit Scope errst_scope with errst.
Module MonadNotations.
Notation "x <- c1 ;; c2" := (@st_bind _ _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : state_scope.

Notation "x <-- y <-- Heq <-- c1 ;; c2" := (@st_bind_dep _ _ _ c1 (fun x y Heq => c2))
  (at level 61, c1 at next level, right associativity) : state_scope.

Notation "x <- c1 ;; c2" := (@err_bnd _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : err_scope.

Notation "x <- c1 ;; c2" := (@errst_bind _ _ _ (fun x => c2) c1)
  (at level 61, c1 at next level, right associativity) : errst_scope.
End MonadNotations.

(*Combining 2 states*)
Definition st_lift1 {B A C: Type} (s1: st A C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s1) (fst t) in
    (res, (i, snd t))).
Definition st_lift2 {A B C: Type} (s2: st B C) : st (A * B) C :=
  mkState (fun (t: A * B) => 
    let (res, i) := (runState s2) (snd t) in
    (res, (fst t, i))).

(*Notation for counter*)
Notation ctr a := (st CoqBigInt.t a).
(*Counter + error handling*)
Notation ctrErr A := (errState (CoqBigInt.t) A).

(*Utility Functions*)
Import MonadNotations.

(*We need lots of e.g. folding and mapping over lists.
  The functions we need are often identical, but we need multiple
  versions to avoid Obj.magic (unless we can evaluate before extraction)*)

Local Open Scope err_scope.
(*Note: fold right, not left*)
(*Version that can be used in nested recursive defs*)
Definition foldr_err := fun {A B: Type} (f: A -> B -> errorM A) =>
  fix fold_errorM (l: list B) (x: A) {struct l} :=
  match l with
  | nil => err_ret x
  | h :: t =>
    i <- fold_errorM t x ;;
    f i h
  end.

Definition foldl_err {A B: Type}
  (f: A -> B -> errorM A) :=
  fix foldM (l: list B) (x: A) :=
  match l with
  | nil => err_ret x
  | h :: t =>
    (j <- f x h ;;
    foldM t j)%err
  end.

Definition fold_left2_err {A B C : Type} 
  (f: C -> A -> B -> errorM C) :=
  fix foldM (accu: C) (l1: list A) (l2: list B) : errorM (option C) :=
  match l1, l2 with
  | nil, nil => err_ret (Some accu)
  | a1 :: l1, a2 :: l2 => 
    (x <- (f accu a1 a2) ;;
    foldM x l1 l2)%err
  | _, _ => err_ret None
  end.

Definition iter_err {A: Type}
  (f: A -> errorM unit) (l: list A) : errorM unit :=
  foldl_err (fun _ x => f x) l tt.

Definition iter2_err {A B: Type} (f: A -> B -> errorM unit) (l1: list A) (l2: list B) : errorM unit :=
  o <- fold_left2_err (fun _ x y => f x y) tt l1 l2 ;;
  match o with
  | None => throw (Invalid_argument "iter2")
  | Some x => err_ret x
  end.

Local Open Scope state_scope.
Definition foldl_st := fun {S1 A B: Type} (f: A -> B -> st S1 A) =>
  fix foldl_st (l: list B) (x: A) {struct l} :=
  match l with
  | nil => st_ret x
  | h :: t => j <- f x h ;;
              foldl_st t j
  end.

Definition iter_st {S A: Type}
  (f: A -> st S unit) (l: list A) : st S unit :=
  foldl_st (fun _ x => f x) l tt.

Local Open Scope errst_scope.

Definition foldr_errst := fun {S1 A B: Type} (f: B -> A -> errState S1 A) (base: A) =>
  fix fold_right_errst (l: list B) {struct l} :=
  match l with
  | nil => errst_ret base
  | h :: t => r <- fold_right_errst t ;;
              f h r
  end.

Definition foldl_errst := fun {S1 A B: Type} (f: A -> B -> errState S1 A) =>
  fix fold_left_errst (l: list B) (x: A) {struct l} :=
  match l with
  | nil => errst_ret x
  | h :: t => j <- f x h ;;
              fold_left_errst t j
  end.

Fixpoint fold_left2_errst {A B C S : Type} 
  (f: C -> A -> B -> errState S C) (accu: C) 
  (l1: list A) (l2: list B) : errState S (option C) :=
  match l1, l2 with
  | nil, nil => errst_lift2 (err_ret (Some accu))
  | a1 :: l1, a2 :: l2 => 
    (x <- (f accu a1 a2) ;;
    fold_left2_errst f x l1 l2)%errst
  | _, _ => errst_lift2 (err_ret None)
  end.

Definition map2_errst {A B C St: Type} (f: A -> B -> errState St C) :=
  fix map2 (l1: list A) (l2: list B) : errState St (option (list C)) :=
    match l1, l2 with
    | nil, nil => errst_ret (Some nil)
    | x1 :: t1, x2 :: t2 => 
      y <- f x1 x2 ;;
      o <- map2 t1 t2 ;;
      match o with
      | Some ys => errst_ret (Some (y :: ys))
      | None => errst_ret None
      end
    | _, _ => errst_ret None
    end.
