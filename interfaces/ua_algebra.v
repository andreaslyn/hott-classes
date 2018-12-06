Require Export HoTTClasses.interfaces.ua_signature.

Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Basics.Equivalences
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.Types.Arrow
  HoTT.Types.Forall
  HoTT.Types.Universe
  HoTT.HSet
  HoTT.Classes.interfaces.abstract_algebra.

Import ne_list.notations.

Declare Scope Algebra_scope.
Delimit Scope Algebra_scope with Algebra.

Notation Carriers := (λ (σ : Signature), sort σ → Type).

Fixpoint Operation {σ : Signature} (A : Carriers σ) (u : symboltype σ) : Type
  := match u with
     | [:s] => A s
     | s ::: u' => A s → Operation A u'
     end.

Global Instance hset_operation `{Funext} {σ : Signature} (A : Carriers σ)
    `{!∀ s, IsHSet (A s)} (w : symboltype σ)
    : IsHSet (Operation A w).
Proof.
  induction w; apply (istrunc_trunctype_type 0).
Defined.

Record Algebra {σ : Signature} : Type := BuildAlgebra
  { carriers : Carriers σ
  ; operations : ∀ (u : symbol σ), Operation carriers (σ u)
  ; hset_carriers_algebra : ∀ (s : sort σ), IsHSet (carriers s) }.

Arguments Algebra : clear implicits.
Arguments BuildAlgebra {σ} carriers operations {hset_carriers_algebra}.

Global Coercion carriers : Algebra >-> Funclass.

Global Existing Instance hset_carriers_algebra.

Definition SigAlgebra (σ : Signature) : Type :=
  {carriers : Carriers σ
  | {operations : ∀ (u : symbol σ), Operation carriers (σ u)
    | ∀ (s : sort σ), IsHSet (carriers s)}}.

Lemma issig_algebra {σ} : Algebra σ <~> SigAlgebra σ.
Proof.
  apply symmetric_equiv.
  unfold SigAlgebra.
  issig (@BuildAlgebra σ)
          (@carriers σ) (@operations σ) (@hset_carriers_algebra σ).
Defined.

Lemma issig_algebra_property {σ} (A : Algebra σ) :
  ∀ (P : ∀ (c : Carriers σ), (∀ (u : symbol σ), Operation c (σ u)) → Type),
  P ((issig_algebra A).1) ((issig_algebra A).2.1) →
  P A (operations A).
Proof.
  trivial.
Defined.

Lemma path_algebra `{Funext} {σ} (A B : Algebra σ)
  : (∃ (p : carriers A = carriers B),
     transport (λ X, ∀ u, Operation X (σ u)) p (operations A) = operations B)
  → A = B.
Proof.
  intro s.
  apply ((ap issig_algebra)^-1).
  generalize dependent s.
  repeat apply issig_algebra_property.
  intros [p q].
  refine (path_sigma _ _ _ p _).
  apply path_sigma_hprop.
  by path_induction.
Defined.

Module algebra_notations.
  Export signature_notations.

  Global Notation "u ^^ A" := (operations A u) (at level 15, no associativity)
    : Algebra_scope.

  Global Open Scope Algebra_scope.
End algebra_notations.
