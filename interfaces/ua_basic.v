Require HoTTClasses.implementations.ne_list.
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
  HoTT.Basics.Equivalences.

Import ne_list.notations.

(* When canonical_names.v has been removed, this line can be removed as well. *)
Open Scope type_scope.

Record Signature : Type := BuildSignature
  { sign_sort : Type
  ; sign_symbol : Type
  ; sign_symbol_type : sign_symbol → ne_list sign_sort }.

Global Coercion sign_symbol_type : Signature >-> Funclass.

Definition BuildSingleSortedSignature {Op : Type} (arities : Op → nat)
  : Signature
  := BuildSignature Unit Op (ne_list.replicate_Sn tt ∘ arities).

Definition op_symbol_type (σ : Signature) : Type := ne_list (sign_sort σ).

Definition op_symbol_cod {σ} : op_symbol_type σ → sign_sort σ := ne_list.last.

Definition op_symbol_dom {σ} : op_symbol_type σ → list (sign_sort σ)
  := ne_list.front.

Definition op_symbol_arity {σ} (w : op_symbol_type σ) : nat
  := length (op_symbol_dom w).

Notation Carriers := (λ (σ : Signature), sign_sort σ → Type).

Fixpoint op_type {σ : Signature} (A : Carriers σ) (u : op_symbol_type σ) : Type
  := match u with
     | ne_list.one s => A s
     | ne_list.cons s u' => A s → op_type A u'
     end.

Global Instance trunc_op_type {Fu : Funext} {σ : Signature} (A : Carriers σ)
    `{Is : ∀ s, IsHSet (A s)} (w : op_symbol_type σ)
    : IsHSet (op_type A w).
Proof.
  induction w; apply (istrunc_trunctype_type 0).
Defined.

Definition Algebra (σ : Signature) : Type :=
  ∃ (carriers : Carriers σ)
    (algebra_op : ∀ (u : sign_symbol σ), op_type carriers (σ u)),
    ∀ (s : sign_sort σ), IsHSet (carriers s).

Existing Class Algebra.

Definition carriers {σ} (A : Algebra σ) : Carriers σ := A.1.

Definition algebra_op {σ} (A : Algebra σ) : ∀ u, op_type (carriers A) (σ u)
  := A.2.1.

Global Instance hset_algebra_carriers {σ} (A : Algebra σ)
  : ∀ s, IsHSet (carriers A s)
  := A.2.2.

Definition BuildAlgebra {σ} (carriers : Carriers σ)
    (algebra_op : ∀ (u : sign_symbol σ), op_type carriers (σ u))
    {S : ∀ (s : sign_sort σ), IsHSet (carriers s)}
  : Algebra σ
  := (carriers; (algebra_op; S)).

Global Coercion carriers : Algebra >-> Funclass.

Definition pair_algebra {σ} (A B : Algebra σ) : Type :=
  ∃ (p : carriers A = carriers B),
  transport (λ C, ∀ u, op_type C (σ u)) p (algebra_op A) = algebra_op B.

Local Lemma path_transport_proj1_sig {A : Type} {x y : A} {P Q : A → Type}
  {u : ∃ (_ : P x), Q x} (p : x = y)
  : transport (λ x : A, P x) p u.1 =
    (transport (λ x : A, ∃ (y : P x), Q x) p u).1.
Proof.
  by path_induction.
Defined.

Lemma path_pair_algebra_algebra `{Funext} {σ} (A B : Algebra σ)
  : pair_algebra A B → A = B.
Proof.
  intros [p q].
  refine (path_sigma _ _ _ p _).
  apply path_sigma_hprop.
  exact ((path_transport_proj1_sig p)^ @ q).
Defined.

Lemma path_algebra_path_algebra {σ} (A B : Algebra σ)
  : A = B → pair_algebra A B.
Proof.
  path_induction. exact (idpath; idpath).
Defined.

Module algebra_notations.
  Notation "u ^^ A" := (algebra_op A u) (at level 15, no associativity).
End algebra_notations.
