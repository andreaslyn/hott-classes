Require HoTTClasses.implementations.ne_list.
Require Import
  Coq.Unicode.Utf8
  Classes.implementations.list
  HoTT.Classes.interfaces.abstract_algebra.

Import ne_list.notations.

Section function_symbol.
  Variable Sort : Type.

  (* For single-sorted algebras, Sort will typically be unit. *)

  (* [fn_symbol_type] describes the type of a function symbol in a signature. Note that higher order function types are excluded: *)

  Definition fn_symbol_type : Type := ne_list Sort.

  Definition fn_symbol_codomain : fn_symbol_type → Sort := ne_list.last.

  Definition fn_symbol_domain : fn_symbol_type → list Sort := ne_list.front.

  Definition fn_symbol_arity : fn_symbol_type → nat := length ∘ fn_symbol_domain.
End function_symbol.

Record Signature : Type := BuildSignature
  { sig_sort : Type
  ; sig_symbol :> Type
  ; sig_symbol_type :> sig_symbol → fn_symbol_type sig_sort }.

Definition sig_fn_type (σ : Signature) : Type := fn_symbol_type (sig_sort σ).

Definition build_single_sorted_signature {Op : Type} (arities : Op → nat)
  : Signature
  := BuildSignature Unit Op (ne_list.replicate_Sn tt ∘ arities).

Notation Carriers := (λ (σ : Signature), sig_sort σ → Type).

Fixpoint op_type {σ : Signature} (A : Carriers σ) (u : sig_fn_type σ) : Type :=
  match u with
  | ne_list.one s => A s
  | ne_list.cons s u' => A s → op_type A u'
  end.

Global Instance op_type_hset {Fu : Funext} (σ : Signature) (A : Carriers σ)
    `{Is : ∀ s, IsHSet (A s)} (u : sig_fn_type σ)
    : IsHSet (op_type A u).
Proof. induction u; apply (istrunc_trunctype_type 0). Defined.

Class IsAlgebra {σ: Signature} (A : Carriers σ) : Type :=
  { algebra_ishset :> ∀ (s : sig_sort σ), IsHSet (A s)
  ; algebra_op : ∀ (u : sig_symbol σ), op_type A (σ u) }.

Arguments algebra_op {σ} A {IsAlgebra}.

Class Algebra (σ : Signature) : Type := BuildAlgebra
  { algebra_carriers : Carriers σ
  ; algebra_isalgebra :> IsAlgebra algebra_carriers }.

Arguments BuildAlgebra {σ} algebra_carriers {algebra_isalgebra}.
Arguments algebra_carriers {σ}.

Definition algebra_carriers_coercion {σ} : Algebra σ → Carriers σ
  := algebra_carriers.

Global Coercion algebra_carriers_coercion : Algebra >-> Funclass.
