(* TODO. This needs to be ported.
Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.universal_algebra
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Spaces.Nat.

Inductive op := mult.

Definition sig: Signature := single_sorted_signature
  (λ u, match u with mult => 2%nat end).

Section laws.
  Global Instance: SgOp (Term0 sig nat tt) :=
    λ x, App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Type :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.

Global Instance encode_operations A `{!SgOp A}: AlgebraOps sig (const A) :=
  λ u, match u with mult => (&) end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: SgOp (A tt) := algebra_op mult.
End decode_operations.

Section encode_variety_and_ops.
  Context A `{SemiGroup A}.

  Global Instance encode_algebra_and_ops: Algebra sig (const A).
  Proof. intros []; simpl; apply _. Qed.

  Global Instance encode_variety_and_ops: InVariety theory (const A).
  Proof.
   constructor. apply _.
   intros ? [] ?; simpl; unfold algebra_op; simpl.
   apply associativity.
  Qed.
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{!SemiGroup (A tt)}: Algebra theory A .
Proof. intros []; simpl in *; try apply _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: SemiGroup (A tt).
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
 match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor; try apply _.
 intro. apply (laws _ e_mult_assoc).
Qed.
*)
