(** This file defines what an [Algebra] is and provides some
    elementary results. *)

Require Export
  Coq.Unicode.Utf8
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

(** A [Signature] is used to characterise [Algebra]s. It consists of
    - A type of [Sort]s, which represent the "objects" (types) an
      algebra for the signature must provide.
    - A type of Function [Symbol]s, which represent operations an
      algebra for the signature must provide.
    - For each symbol [u:Symbol], a [SymbolType] specifying the
      required type of the operation corresponding to [u] provided by
      the algebra for the signature. *)

Record Signature : Type := BuildSignature
  { Sort : Type
  ; Symbol : Type
  ; symbol_types : Symbol → SymbolType_internal Sort }.

(** Notice we have this implicit coercion allowing us to use a
    signature [σ:Signature] as a map [Symbol σ → SymbolType σ]
    (see [SymbolType] below). *)

Global Coercion symbol_types : Signature >-> Funclass.

(** A single sorted [Signature] is a singuture with [Sort = Unit]. *)

Definition BuildSingleSortedSignature (sym : Type) (arities : sym → nat)
  : Signature
  := BuildSignature Unit sym (ne_list.replicate_Sn tt ∘ arities).

(** Let [σ:Signature]. For each symbol [u : Symbol σ], [σ u]
    associates [u] to a [SymbolType σ]. This represents the required
    type of the algebra operation corresponding to [u]. *)

Definition SymbolType (σ : Signature) : Type
  := SymbolType_internal (Sort σ).

(** For [s : SymbolType σ], [cod_symboltype σ] is the codomain of the
    symbol type [s]. *)

Definition cod_symboltype {σ} : SymbolType σ → Sort σ
  := ne_list.last.

(** For [s : SymbolType σ], [cod_symboltype σ] is the domain of the
    symbol type [s]. *)

Definition dom_symboltype {σ} : SymbolType σ → list (Sort σ)
  := ne_list.front.

(** For [s : SymbolType σ], [cod_symboltype σ] is the arity of the
    symbol type [s]. That is the number [n:nat] of arguments of the
    [SymbolType σ]. *)

Definition arity_symboltype {σ} : SymbolType σ → nat
  := length ∘ dom_symboltype.

(** An [Algebra] must provide a family of [Carriers σ] indexed by
    [Sort σ]. These carriers are the "objects" (types) of the algebra. *)

(* [Carriers] is a notation because it will be used for an implicit
   coercion [Algebra >-> Funclass] below. *)

Notation Carriers := (λ (σ : Signature), Sort σ → Type).

(** The function [Operation] maps a family of carriers [A : Carriers σ]
    and [w : SymbolType σ] to the corresponding function type. For
    example

    <<
      Operation A [:s1; s2; r:] = A s1 → A s2 → A r
    >> *)

Fixpoint Operation {σ : Signature} (A : Carriers σ) (w : SymbolType σ)
  : Type
  := match w with
     | [:s:] => A s
     | s ::: w' => A s → Operation A w'
     end.

Global Instance trunc_operation `{Funext} {σ : Signature}
  (A : Carriers σ) {n} `{!∀ s, IsTrunc n (A s)} (w : SymbolType σ)
  : IsTrunc n (Operation A w).
Proof.
  induction w; apply (istrunc_trunctype_type (BuildTruncType n _)).
Defined.

(** Uncurry of an [f : Operation A w], such that

    <<
      ap_operation f (x1,x2,...,xn) = f x1 x2 ... xn
    >> *)

Fixpoint ap_operation {σ} {A : Carriers σ} {w : SymbolType σ}
    : Operation A w →
      FamilyProd A (dom_symboltype w) →
      A (cod_symboltype w)
    := match w with
       | [:s:] => λ f _, f
       | s ::: w' => λ f '(x, l), ap_operation (f x) l
       end.

(** Funext for uncurried [Operation A w]. If

    <<
      ap_operation f (x1,x2,...,xn) = ap_operation g (x1,x2,...,xn)
    >>
    for all [(x1,x2,...,xn) : A s1 * A s2 * ... * A sn], then [f = g]. *)

Fixpoint path_forall_ap_operation `{Funext} {σ : Signature}
  {A : Carriers σ} {w : SymbolType σ}
  : ∀ (f g : Operation A w),
    (∀ a : FamilyProd A (dom_symboltype w),
       ap_operation f a = ap_operation g a)
    -> f = g
  := match w with
     | [:s:] => λ (f g : A s) p, p tt
     | s ::: w' =>
         λ (f g : A s → Operation A w') p,
          path_forall f g
            (λ x, path_forall_ap_operation (f x) (g x) (λ a, p (x,a)))
     end.

(** An [Algebra σ] for a signature [σ] consists of a family [carriers :
    Carriers σ] indexed by the sorts [s : Sort σ], and for each symbol
    [u : Symbol σ], an operation of type [Operation carriers (σ u)],
    where [σ u : SymbolType σ] is the symbol type of [u]. For each
    sort [s : Sort σ], [carriers s] is required to be a set. *)

Record Algebra {σ : Signature} : Type := BuildAlgebra
  { carriers : Carriers σ
  ; operations : ∀ (u : Symbol σ), Operation carriers (σ u)
  ; hset_carriers_algebra : ∀ (s : Sort σ), IsHSet (carriers s) }.

Arguments Algebra : clear implicits.

Arguments BuildAlgebra {σ} carriers operations {hset_carriers_algebra}.

(** We have a convenient implicit coercion from an algebra to the
    family of carriers. *)
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

(** To find a path between two algebras [A B : Algebra σ] it suffices
    to find a path between the carrier families and the operations. *)

Lemma path_algebra `{Funext} {σ} (A B : Algebra σ)
  : (∃ (p : carriers A = carriers B),
       transport (λ X, ∀ u, Operation X (σ u)) p (operations A)
       = operations B)
  → A = B.
Proof.
  intros [p q].
  apply ((ap issig_algebra)^-1).
  change_issig_algebra A. change_issig_algebra B.
  refine (path_sigma _ _ _ p _).
  apply path_sigma_hprop.
  by path_induction.
Defined.

Module algebra_notations.

(** Given [A : Algebra σ] and function symbol [u : Symbol σ], we use
    the notation [u ^^ A] to refer to the algebra operation
    corresponding to the symbol [u]. *)

  Global Notation "u ^^ A" := (operations A u) (at level 60, no associativity)
    : Algebra_scope.

End algebra_notations.
