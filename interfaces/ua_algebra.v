Require Export HoTTClasses.interfaces.ua_signature.

Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.Types.Arrow
  HoTT.Types.Forall
  HoTT.Types.Universe
  HoTT.HSet
  HoTT.Basics.Equivalences
  HoTT.Classes.interfaces.abstract_algebra.

Import ne_list.notations.

Declare Scope Algebra_scope.
Delimit Scope Algebra_scope with Algebra.

Local Notation "'Carriers_internal' σ" := (sort σ → Type) (at level 10).

Definition Carriers (σ : Signature) : Type := Carriers_internal σ.

Fixpoint op_type {σ : Signature} (A : Carriers σ) (u : symboltype σ) : Type
  := match u with
     | [:s:] => A s
     | s ::: u' => A s → op_type A u'
     end.

Global Instance hset_op_type `{Funext} {σ : Signature} (A : Carriers σ)
    `{!∀ s, IsHSet (A s)} (w : symboltype σ)
    : IsHSet (op_type A w).
Proof.
  induction w; apply (istrunc_trunctype_type 0).
Defined.

Definition Algebra (σ : Signature) : Type :=
  ∃ (carriers : Carriers σ)
    (ops : ∀ (u : symbol σ), op_type carriers (σ u)),
    ∀ (s : sort σ), IsHSet (carriers s).

Definition carriers_algebra {σ} : Algebra σ → Carriers σ := pr1.

Local Definition coercion_carriers_algebra {σ}
  : Algebra σ → Carriers_internal σ
  := carriers_algebra.

Global Coercion coercion_carriers_algebra : Algebra >-> Funclass.

Definition ops_algebra {σ} (A : Algebra σ)
  : ∀ u, op_type (carriers_algebra A) (σ u)
  := A.2.1.

Global Instance hset_algebra_carriers {σ} (A : Algebra σ)
  : ∀ s, IsHSet (carriers_algebra A s)
  := A.2.2.

Definition BuildAlgebra {σ} (carriers : Carriers σ)
    (ops : ∀ (u : symbol σ), op_type carriers (σ u))
    {S : ∀ (s : sort σ), IsHSet (carriers s)}
  : Algebra σ
  := (carriers; (ops; S)).

Definition sig_path_algebra {σ} (A B : Algebra σ) : Type :=
  ∃ (p : carriers_algebra A = carriers_algebra B),
  transport (λ C, ∀ u, op_type C (σ u)) p (ops_algebra A) = ops_algebra B.

Local Lemma path_transport_pr1 {A : Type} {x y : A} {P Q : A → Type}
  {u : ∃ (_ : P x), Q x} (p : x = y)
  : transport (λ x : A, P x) p u.1 =
    (transport (λ x : A, ∃ (y : P x), Q x) p u).1.
Proof.
  by path_induction.
Defined.

Lemma path_sig_path_algebra_algebra `{Funext} {σ} (A B : Algebra σ)
  : sig_path_algebra A B → A = B.
Proof.
  intros [p q].
  refine (path_sigma _ _ _ p _).
  apply path_sigma_hprop.
  exact ((path_transport_pr1 p)^ @ q).
Defined.

Lemma path_algebra_sig_path_algebra {σ} (A B : Algebra σ)
  : A = B → sig_path_algebra A B.
Proof.
  path_induction. exact (idpath; idpath).
Defined.

Module algebra_notations.
  Export signature_notations.

  Global Notation "u ^^ A" := (ops_algebra A u) (at level 7, no associativity)
    : Algebra_scope.

  Global Open Scope Algebra_scope.
End algebra_notations.
