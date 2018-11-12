Require
  HoTTClasses.implementations.ne_list.
Require Import
  Coq.Unicode.Utf8
  Classes.implementations.list
  HoTT.Classes.interfaces.abstract_algebra.

Import ne_list.notations.

Section with_sorts.
  Variable Sorts: Type0.

  (* For single-sorted algebras, Sorts will typically be unit. *)

  (* OpType describes the type of an operation in an algebra. Note that higher order function types are excluded: *)

  Definition OpType := ne_list Sorts.

  Definition result: OpType → Sorts := @ne_list.last _.

  Variable carrier: Sorts → Type.

  (* Given a Type for each sort, we can map the operation type descriptions to real function types: *)

  Fixpoint op_type (u: OpType): Type :=
    match u with
    | ne_list.one a => carrier a
    | ne_list.cons a g => carrier a → op_type g
    end.

  (* This is just:

      Definition op_type: OpType → Type := ne_list.foldr1 (→) ∘ ne_list.map carrier.

    Unfortunately, in that formulation [simpl] never reduces it, which is extremely annoying...
  *)

End with_sorts.

Arguments op_type {Sorts} _ _.

(*
(* Avoid eager application *)
Hint Extern 0 (Equiv (op_type _ _ )) => eapply @op_type_equiv : typeclass_instances.
*)

Inductive Signature: Type :=
  { sorts: Type0
  ; operation:> Type0
  ; operation_type:> operation → OpType sorts }.

Definition single_sorted_signature {Op: Type0} (arities: Op → nat): Signature :=
  Build_Signature Unit Op (ne_list.replicate_Sn tt ∘ arities).

(* An implementation of a signature for a given realization of the sorts is simply a
 function (of the right type) for each operation: *)

Class AlgebraOps (σ: Signature) (A: sorts σ → Type) := algebra_op: ∀ u, op_type A (σ u).

Class Algebra
  (σ: Signature)
  (carriers: sorts σ → Type)
  `{AlgebraOps σ carriers}: Type :=
    { algebra_set:> ∀ a, IsHSet (carriers a) }.
