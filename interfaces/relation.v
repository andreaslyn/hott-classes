Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Record
  HoTT.Classes.interfaces.abstract_algebra.

Definition RespectsRelation {A B : Type} (R : relation A) (f : A → B)
  : Type
  := ∀ (x y : A), R x y → f x = f y.

Global Instance trunc_reflexive_relation `{Funext} {A : Type}
  (R : relation A) {n} `{!∀ (x y : A), IsTrunc n (R x y)}
  :  IsTrunc n (Reflexive R).
Proof.
  apply trunc_forall.
Defined.

Global Instance trunc_symmetric_relation `{Funext} {A : Type}
  (R : relation A) {n} `{!∀ (x y : A), IsTrunc n (R x y)}
  :  IsTrunc n (Symmetric R).
Proof.
  apply trunc_forall.
Defined.

Global Instance trunc_transitive_relation `{Funext} {A : Type}
  (R : relation A) {n} `{!∀ (x y : A), IsTrunc n (R x y)}
  :  IsTrunc n (Transitive R).
Proof.
  apply trunc_forall.
Defined.

Definition SigEquivalence {A:Type} (R : relation A) : Type :=
  {_ : Reflexive R | { _ : Symmetric R | Transitive R}}.

Lemma issig_equivalence {A:Type} (R : relation A)
  : Equivalence R <~> SigEquivalence R.
Proof.
  apply symmetric_equiv.
  unfold SigEquivalence.
  issig (@Build_Equivalence A R) (@Equivalence_Reflexive A R)
          (@Equivalence_Symmetric A R) (@Equivalence_Transitive A R).
Defined.

Global Instance trunc_equivalence `{Funext} {A : Type}
  (R : relation A) {n} `{!∀ (x y : A), IsTrunc n (R x y)}
  : IsTrunc n (Equivalence R).
Proof.
  exact (trunc_equiv (SigEquivalence R) (issig_equivalence R)^-1).
Qed.
