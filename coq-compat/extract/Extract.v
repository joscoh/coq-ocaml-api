From CoqCompat Require Import ExtractUtil.

(*Unset Extraction Optimize.*)
(*TODO*)
Separate Extraction (*CoqUtil.str_to_pos*) (*TEMP*)
  State CoqCtr.
  (* CoqExthtbl NumberDefs NumberFuncs hashcons extmap extset CoqHashtbl 
  CoqWstdlib
  ConstantDefs IdentDefs TyDefs TyFuncs TermDefs TermFuncs
  DeclDefs DeclFuncs CoercionDefs TheoryDefs TheoryFuncs TaskDefs TaskFuncs TransDefs
  EliminateInductive EliminateDefinition. *)
(* TheoryDefs.*) (*Ty.ty_v_map Ident.*)
(*Separate Extraction Extmap.
Separate Extraction Ty.ty Ty.ty_v_map Ident.*)