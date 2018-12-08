(* TODO. This needs to be ported.
Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.universal_algebra
  HoTTClasses.theory.ua_homomorphisms
  HoTT.Spaces.Nat
  HoTT.Basics.Equivalences.

Inductive op := mult | one.

Definition sig: Signature := single_sorted_signature
  (λ u, match u with one => O | mult => 2%nat end).

Section laws.
  Global Instance: SgOp (Term0 sig nat tt) :=
    fun x => App sig _ _ _ (App sig _ _ _ (Op sig nat mult) x).
  Global Instance: MonUnit (Term0 sig nat tt) := Op sig nat one.

  Local Notation x := (Var sig nat 0%nat tt).
  Local Notation y := (Var sig nat 1%nat tt).
  Local Notation z := (Var sig nat 2%nat tt).

  Import notations.

  Inductive Laws: EqEntailment sig → Type :=
    | e_mult_assoc: Laws (x & (y & z) === (x & y) & z)
    | e_mult_1_l: Laws (mon_unit & x === x)
    | e_mult_1_r: Laws (x & mon_unit === x).
End laws.

Definition theory: EquationalTheory := Build_EquationalTheory sig Laws.

Local Hint Extern 3 => progress simpl : typeclass_instances.

Instance encode_operations A `{!SgOp A} `{!MonUnit A}: AlgebraOps sig (λ _, A) :=
  λ u, match u with mult => (&) | one => mon_unit: A end.

Section decode_operations.
  Context `{AlgebraOps theory A}.
  Global Instance: MonUnit (A tt) := algebra_op one.
  Global Instance: SgOp (A tt) := algebra_op mult.
End decode_operations.

Section encode_variety_and_ops.
  Context A `{Monoid A}.

  Global Instance encode_algebra_and_ops: Algebra sig _.
  Proof. intro. exact _. Qed.

  Global Instance encode_variety_and_ops: InVariety theory (const A) | 10.
  Proof.
   constructor. exact _.
   intros ? [] ?; simpl; unfold algebra_op; simpl.
     apply associativity.
    apply left_identity.
   apply right_identity.
  Qed.
End encode_variety_and_ops.

Lemma encode_algebra_only `{!AlgebraOps theory A} `{!Monoid (A tt)}: Algebra theory A .
Proof. intros []; exact _. Qed.

Global Instance decode_variety_and_ops `{InVariety theory A}: Monoid (A tt) | 10.
Proof with simpl; auto.
 pose proof (λ law lawgood x y z, variety_laws law lawgood (λ s n,
 match s with tt => match n with 0 => x | 1 => y | _ => z end end)) as laws.
 constructor.
 constructor.
 exact _.
 intro. apply (laws _ e_mult_assoc).
 intro. apply (laws _ e_mult_1_l mon_unit y y)...
 intro. apply (laws _ e_mult_1_r x mon_unit x)...
Qed.
*)
