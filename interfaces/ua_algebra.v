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

Definition Algebra (σ : Signature) : Type :=
  ∃ (carriers : Carriers σ)
    (operations : ∀ (u : symbol σ), Operation carriers (σ u)),
    ∀ (s : sort σ), IsHSet (carriers s).

Definition carriers {σ} : Algebra σ → Carriers σ := pr1.

Global Coercion carriers : Algebra >-> Funclass.

Definition operations {σ} (A : Algebra σ)
  : ∀ u, Operation (carriers A) (σ u)
  := A.2.1.

Global Instance hset_carriers_algebra {σ} (A : Algebra σ)
  : ∀ s, IsHSet (carriers A s)
  := A.2.2.

Definition BuildAlgebra {σ} (carriers : Carriers σ)
    (ops : ∀ (u : symbol σ), Operation carriers (σ u))
    {S : ∀ (s : sort σ), IsHSet (carriers s)}
  : Algebra σ
  := (carriers; (ops; S)).

Lemma path_transport_proj1_sig {A : Type} {x y : A} {P Q : A → Type}
  {u : ∃ (_ : P x), Q x} (p : x = y)
  : transport (λ x : A, P x) p u.1 =
    (transport (λ x : A, ∃ (y : P x), Q x) p u).1.
Proof.
  by path_induction.
Defined.

Lemma path_algebra `{Funext} {σ} (A B : Algebra σ)
  : (∃ (p : carriers A = carriers B),
     transport (λ X, ∀ u, Operation X (σ u)) p (operations A) = operations B)
  → A = B.
Proof.
  intros [p q].
  refine (path_sigma _ _ _ p _).
  apply path_sigma_hprop.
  exact ((path_transport_proj1_sig p)^ @ q).
Defined.

Module algebra_notations.
  Export signature_notations.

  Global Notation "u ^^ A" := (operations A u) (at level 15, no associativity)
    : Algebra_scope.

  Global Open Scope Algebra_scope.
End algebra_notations.
