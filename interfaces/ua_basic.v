Require HoTTClasses.implementations.ne_list.
Require Import
  Coq.Unicode.Utf8
  Classes.implementations.list
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.Types.Arrow
  HoTT.Types.Forall
  HoTT.HSet.

Import ne_list.notations.

Section function_symbol.
  Variable Sort : Type.

  (* For single-sorted algebras, Sort will typically be unit. *)

  (* [op_symbol_type] describes the type of a function symbol in a signature. Note that higher order function types are excluded: *)

  Definition op_symbol_type : Type := ne_list Sort.

  Definition op_symbol_cod : op_symbol_type → Sort := ne_list.last.

  Definition op_symbol_dom : op_symbol_type → list Sort := ne_list.front.

  Definition op_symbol_arity : op_symbol_type → nat := length ∘ op_symbol_dom.
End function_symbol.

Record Signature : Type := BuildSignature
  { sig_sort : Type
  ; sig_symbol :> Type
  ; sig_symbol_type :> sig_symbol → op_symbol_type sig_sort }.

Definition sig_op_type (σ : Signature) : Type := op_symbol_type (sig_sort σ).

Definition build_single_sorted_signature {Op : Type} (arities : Op → nat)
  : Signature
  := BuildSignature Unit Op (ne_list.replicate_Sn tt ∘ arities).

Notation Carriers := (λ (σ : Signature), sig_sort σ → Type).

Fixpoint op_type {σ : Signature} (A : Carriers σ) (u : sig_op_type σ) : Type :=
  match u with
  | ne_list.one s => A s
  | ne_list.cons s u' => A s → op_type A u'
  end.

Global Instance op_type_hset {Fu : Funext} {σ : Signature} (A : Carriers σ)
    `{Is : ∀ s, IsHSet (A s)} (u : sig_op_type σ)
    : IsHSet (op_type A u).
Proof. induction u; apply (istrunc_trunctype_type 0). Defined.

Class IsAlgebra {σ: Signature} (A : Carriers σ) : Type := BuildIsAlgebra
  { algebra_set :> ∀ (s : sig_sort σ), IsHSet (A s)
  ; algebra_op : ∀ (u : sig_symbol σ), op_type A (σ u) }.

Arguments algebra_op {σ} A {IsAlgebra}.

Lemma isalgebra_sig {σ} (A : Carriers σ) :
  {_ : ∀ s, IsHSet (A s) | ∀ u, op_type A (σ u) } <~> IsAlgebra A.
Proof.
  issig2 (@BuildIsAlgebra σ A) (@algebra_set σ A) (@algebra_op σ A).
Defined.

Global Instance isalgebra_hset {Fu : Funext} {σ} (A : Carriers σ)
    : IsHSet (IsAlgebra A).
Proof. apply (@trunc_equiv _ _ (isalgebra_sig A)); apply _. Defined.

Record Algebra (σ : Signature) : Type := BuildAlgebra
  { algebra_carriers : Carriers σ
  ; algebra_isalgebra : IsAlgebra algebra_carriers }.

Existing Class Algebra.
Global Existing Instance algebra_isalgebra.

Arguments BuildAlgebra {σ} algebra_carriers {algebra_isalgebra}.
Arguments algebra_carriers {σ}.
Arguments algebra_isalgebra {σ}.

Definition algebra_carriers_coercion {σ} : Algebra σ → Carriers σ
  := algebra_carriers.

Global Coercion algebra_carriers_coercion : Algebra >-> Funclass.

Global Coercion algebra_sig_coercion {σ} (A : Algebra σ) : Type
  := (∀ s, algebra_carriers A s) * IsAlgebra A.

(*
Lemma algebra_sig (σ : Signature) :
  {A : Carriers σ | IsAlgebra A } <~> Algebra σ.
Proof.
  issig2 (@BuildAlgebra σ) (@algebra_carriers σ) (@algebra_isalgebra σ).
Defined.
*)
