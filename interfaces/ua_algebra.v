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

Notation Carriers := (λ (σ : Signature), Sort σ → Type).

Fixpoint Operation {σ : Signature} (A : Carriers σ) (u : SymbolType σ) : Type
  := match u with
     | [:s] => A s
     | s ::: u' => A s → Operation A u'
     end.

Global Instance hset_operation `{Funext} {σ : Signature} (A : Carriers σ)
    `{!∀ s, IsHSet (A s)} (w : SymbolType σ)
    : IsHSet (Operation A w).
Proof.
  induction w; apply (istrunc_trunctype_type 0).
Defined.

Record Algebra {σ : Signature} : Type := BuildAlgebra
  { carriers : Carriers σ
  ; operations : ∀ (u : Symbol σ), Operation carriers (σ u)
  ; hset_carriers_algebra : ∀ (s : Sort σ), IsHSet (carriers s) }.

Arguments Algebra : clear implicits.
Arguments BuildAlgebra {σ} carriers operations {hset_carriers_algebra}.

Global Coercion carriers : Algebra >-> Funclass.

Global Existing Instance hset_carriers_algebra.

Definition SigAlgebra (σ : Signature) : Type :=
  {carriers : Carriers σ
  | {operations : ∀ (u : Symbol σ), Operation carriers (σ u)
    | ∀ (s : Sort σ), IsHSet (carriers s)}}.

Lemma issig_algebra {σ} : Algebra σ <~> SigAlgebra σ.
Proof.
  apply symmetric_equiv.
  unfold SigAlgebra.
  issig (@BuildAlgebra σ) (@carriers σ) (@operations σ)
    (@hset_carriers_algebra σ).
Defined.

Lemma path_issig_algebra {σ} (A B : Algebra σ)
  : issig_algebra A = issig_algebra B → A = B.
Proof.
  exact ((ap issig_algebra)^-1).
Defined.

Ltac change_issig_algebra A :=
  match type of A with
  | Algebra ?σ =>
      change (@hset_carriers_algebra σ A) with (issig_algebra A).2.2 in *;
      change (@operations σ A) with (issig_algebra A).2.1 in *;
      change (@carriers σ A) with (issig_algebra A).1 in *
  | _ => idtac
  end.

Ltac repeat_change_issig_algebra :=
  match goal with
  | [ A : Algebra ?σ |- _] =>
      progress (change_issig_algebra A); repeat_change_issig_algebra
  | _ => idtac
  end.

Lemma path_algebra `{Funext} {σ} (A B : Algebra σ)
  : (∃ (p : carriers A = carriers B),
     transport (λ X, ∀ u, Operation X (σ u)) p (operations A) = operations B)
  → A = B.
Proof.
  intros [p q].
  apply path_issig_algebra.
  repeat_change_issig_algebra.
  refine (path_sigma _ _ _ p _).
  apply path_sigma_hprop.
  by path_induction.
Defined.

Module algebra_notations.
  Export signature_notations.

  Global Notation "u ^^ A" := (operations A u) (at level 60, no associativity)
    : Algebra_scope.

  Global Open Scope Algebra_scope.
End algebra_notations.
