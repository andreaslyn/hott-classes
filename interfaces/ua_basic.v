Require Import
  Coq.Unicode.Utf8
  Classes.implementations.list
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.Types.Arrow
  HoTT.Types.Forall
  HoTT.Types.Universe
  HoTT.HSet
  HoTT.Basics.Equivalences
  HoTTClasses.implementations.ne_list.

Import nel.notations.

Declare Scope Algebra_scope.
Delimit Scope Algebra_scope with Algebra.

Definition opsym_type' : Type → Type := @nel.

Record Signature : Type := BuildSignature
  { sigsort : Type
  ; sigsym : Type
  ; sigsym_type : sigsym → opsym_type' sigsort }.

Global Coercion sigsym_type : Signature >-> Funclass.

Definition BuildSingleSortedSignature {Op : Type} (arities : Op → nat)
  : Signature
  := BuildSignature Unit Op (nel.replicate_Sn tt ∘ arities).

Definition opsym_type (σ : Signature) : Type := opsym_type' (sigsort σ).

Definition opsym_cod {σ} : opsym_type σ → sigsort σ := nel.last.

Definition opsym_dom {σ} : opsym_type σ → list (sigsort σ) := nel.front.

Definition opsym_arity {σ} : opsym_type σ → nat := length ∘ opsym_dom.

Notation Carriers := (λ (σ : Signature), sigsort σ → Type).

Fixpoint op_type {σ : Signature} (A : Carriers σ) (u : opsym_type σ) : Type
  := match u with
     | [:s:] => A s
     | s ::: u' => A s → op_type A u'
     end.

Global Instance hset_op_type {Fu : Funext} {σ : Signature} (A : Carriers σ)
    `{Is : ∀ s, IsHSet (A s)} (w : opsym_type σ)
    : IsHSet (op_type A w).
Proof.
  induction w; apply (istrunc_trunctype_type 0).
Defined.

Definition Algebra (σ : Signature) : Type :=
  ∃ (carriers : Carriers σ)
    (algop : ∀ (u : sigsym σ), op_type carriers (σ u)),
    ∀ (s : sigsort σ), IsHSet (carriers s).

Existing Class Algebra.

Definition carriers {σ} (A : Algebra σ) : Carriers σ := A.1.

Global Coercion carriers : Algebra >-> Funclass.

Definition algop {σ} (A : Algebra σ) : ∀ u, op_type (carriers A) (σ u)
  := A.2.1.

Global Instance hset_algebra_carriers {σ} (A : Algebra σ)
  : ∀ s, IsHSet (carriers A s)
  := A.2.2.

Definition BuildAlgebra {σ} (carriers : Carriers σ)
    (algop : ∀ (u : sigsym σ), op_type carriers (σ u))
    {S : ∀ (s : sigsort σ), IsHSet (carriers s)}
  : Algebra σ
  := (carriers; (algop; S)).

Module algebra_notations.
  Global Notation "u ^^ A" := (algop A u) (at level 15, no associativity)
    : Algebra_scope.
  Global Open Scope Algebra_scope.
End algebra_notations.

Definition sig_path_algebra {σ} (A B : Algebra σ) : Type :=
  ∃ (p : carriers A = carriers B),
  transport (λ C, ∀ u, op_type C (σ u)) p (algop A) = algop B.

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
