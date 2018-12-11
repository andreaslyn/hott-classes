Require Export
  HoTTClasses.implementations.ne_list
  HoTTClasses.implementations.family_prod.

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
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.implementations.list.

Import ne_list.notations.

Declare Scope Algebra_scope.

Delimit Scope Algebra_scope with Algebra.

Open Scope Algebra_scope.

Local Notation SymbolType_internal := @ne_list.

Record Signature : Type := Build
  { Sort : Type
  ; Symbol : Type
  ; symbol_types : Symbol → SymbolType_internal Sort }.

Global Coercion symbol_types : Signature >-> Funclass.

Definition BuildSingleSortedSignature {Op : Type} (arities : Op → nat)
  : Signature
  := Build Unit Op (ne_list.replicate_Sn tt ∘ arities).

Definition SymbolType (σ : Signature) : Type := SymbolType_internal (Sort σ).

Definition cod_symboltype {σ} : SymbolType σ → Sort σ := ne_list.last.

Definition dom_symboltype {σ} : SymbolType σ → list (Sort σ) := ne_list.front.

Definition arity_symboltype {σ} : SymbolType σ → nat := length ∘ dom_symboltype.

Notation Carriers := (λ (σ : Signature), Sort σ → Type).

Fixpoint Operation {σ : Signature} (A : Carriers σ) (u : SymbolType σ) : Type
  := match u with
     | [:s:] => A s
     | s ::: u' => A s → Operation A u'
     end.

Global Instance trunc_operation `{Funext} {σ : Signature} (A : Carriers σ)
    {n} `{!∀ s, IsTrunc n (A s)} (w : SymbolType σ)
    : IsTrunc n (Operation A w).
Proof.
  induction w; apply (istrunc_trunctype_type (BuildTruncType n _)).
Defined.

(** Uncurry of [Operation], such that

      [ap_operation f (x1,x2,...,xn) = f x1 x2 ... xn]. *)

Fixpoint ap_operation {σ} {A : Carriers σ} {w : SymbolType σ}
    : Operation A w → FamilyProd A (dom_symboltype w) → A (cod_symboltype w)
    := match w with
       | [:s:] => λ f _, f
       | s ::: w' => λ f '(x, l), ap_operation (f x) l
       end.

(** Funext for uncurried [Operation]s. If

      [ap_operation f (x1,x2,...,xn) = ap_operation g (x1,x2,...,xn)],

    for all [(x1,x2,...,xn) : A s1 * A s2 * ... A sn], then [f = g].
*)

Fixpoint path_forall_ap_operation `{Funext} {σ} {A : Carriers σ} {w : SymbolType σ}
  : ∀ (f g : Operation A w),
    (∀ a : FamilyProd A (dom_symboltype w), ap_operation f a = ap_operation g a)
    -> f = g
  := match w with
     | [:s:] => λ f g h, h tt
     | s ::: w' =>
         λ f g h, path_forall f g
                    (λ x, path_forall_ap_operation (f x) (g x) (λ a, h (x,a)))
     end.

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

Ltac change_issig_algebra A :=
  change (hset_carriers_algebra A) with (issig_algebra A).2.2 in *;
  change (operations A) with (issig_algebra A).2.1 in *;
  change (carriers A) with (issig_algebra A).1 in *.

Lemma path_algebra `{Funext} {σ} (A B : Algebra σ)
  : (∃ (p : carriers A = carriers B),
     transport (λ X, ∀ u, Operation X (σ u)) p (operations A) = operations B)
  → A = B.
Proof.
  intros [p q].
  apply ((ap issig_algebra)^-1).
  change_issig_algebra A.
  change_issig_algebra B.
  refine (path_sigma _ _ _ p _).
  apply path_sigma_hprop.
  by path_induction.
Defined.

Module algebra_notations.

  Global Notation "u ^^ A" := (operations A u) (at level 60, no associativity)
    : Algebra_scope.

End algebra_notations.
