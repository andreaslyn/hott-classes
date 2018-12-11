Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Record
  HoTT.Classes.interfaces.abstract_algebra.

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

Ltac change_issig_equivalence E :=
  change (Equivalence_Transitive E) with (issig_equivalence E).2.2 in *;
  change (Equivalence_Symmetric E) with (issig_equivalence E).2.1 in *;
  change (Equivalence_Reflexive E) with (issig_equivalence E).1 in *.

Global Instance trunc_sig_equivalence `{Funext} {A : Type}
  (R : relation A) {n} `{!∀ (x y : A), IsTrunc n (R x y)}
  :  IsTrunc n (SigEquivalence R).
Proof.
  assert (IsTrunc n (Reflexive R)). apply trunc_forall.
  assert (IsTrunc n (Symmetric R)). apply trunc_forall.
  assert (IsTrunc n (Transitive R)). apply trunc_forall.
  assert (IsTrunc n {_ : Symmetric R | Transitive R}).
  apply trunc_sigma.
  apply trunc_sigma.
Qed.

Global Instance trunc_equivalence `{Funext} {A : Type}
  (R : relation A) {n} `{!∀ (x y : A), IsTrunc n (R x y)}
  : IsTrunc n (Equivalence R).
Proof.
  exact (trunc_equiv (SigEquivalence R) (issig_equivalence R)^-1).
Qed.
