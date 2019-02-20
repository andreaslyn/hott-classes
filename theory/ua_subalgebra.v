Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Sigma
  HoTT.Types.Record
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.theory.ua_homomorphism.

Import algebra_notations ne_list.notations.

Section closed_under_op.
  Context {σ} (A : Algebra σ) (P : ∀ (s : Sort σ), A s → hProp).

  Fixpoint ClosedUnderOp {w : SymbolType σ} : Operation A w → Type :=
    match w with
    | [:s:] => P s
    | s ::: w' => λ (α : A s → Operation A w'),
                    ∀ (x : A s), P s x → ClosedUnderOp (α x)
    end.

  Global Instance hprop_op_closed_subalgebra `{Funext}
    {w : SymbolType σ} (α : Operation A w)
    : IsHProp (ClosedUnderOp α).
  Proof.
    induction w; simpl; exact _.
  Defined.

  Definition IsClosedUnderOps : Type
    := ∀ (u : Symbol σ), ClosedUnderOp (u^^A).
End closed_under_op.

Section subalgebra_predicate.
  Context {σ : Signature} (A : Algebra σ).

  Record SubalgebraPredicate : Type := BuildSubalgebraPredicate
    { subalgebra_predicate : ∀ (s : Sort σ), A s → hProp
    ; is_closed_under_ops_subalgebra_predicate
      : IsClosedUnderOps A subalgebra_predicate }.

  Global Coercion subalgebra_predicate
    : SubalgebraPredicate >-> Funclass.

  Definition SigSubalgebraPredicate : Type :=
    { subalgebra_predicate : ∀ (s : Sort σ), A s → hProp
    | IsClosedUnderOps A subalgebra_predicate }.

  Lemma issig_subalgebra_predicate
    : SubalgebraPredicate <~> SigSubalgebraPredicate.
  Proof.
    apply symmetric_equiv.
    unfold SigSubalgebraPredicate.
    issig BuildSubalgebraPredicate subalgebra_predicate
            is_closed_under_ops_subalgebra_predicate.
  Defined.
End subalgebra_predicate.

Arguments BuildSubalgebraPredicate {σ} {A} subalgebra_predicate
            is_closed_under_ops_subalgebra_predicate.

Section subalgebra.
  Context {σ} {A : Algebra σ} (P : SubalgebraPredicate A).

  Definition carriers_subalgebra : Carriers σ
    := λ (s : Sort σ), {x | P s x}.

  Fixpoint op_subalgebra {w : SymbolType σ}
    : ∀ (α : Operation A w),
      ClosedUnderOp A P α → Operation carriers_subalgebra w
    := match w with
       | [:_:] => λ α c, (α; c)
       | _ ::: _ => λ α c x, op_subalgebra (α x.1) (c x.1 x.2)
       end.

  Definition ops_subalgebra (u : Symbol σ)
    : Operation carriers_subalgebra (σ u)
    := op_subalgebra (u^^A) (is_closed_under_ops_subalgebra_predicate A P u).
  
  Definition Subalgebra : Algebra σ
    := BuildAlgebra carriers_subalgebra ops_subalgebra.
End subalgebra.

Global Arguments Subalgebra {σ}.

Module subalgebra_notations.
  Notation "A & P" := (Subalgebra A P) (at level 50, left associativity)
    : Algebra_scope.
End subalgebra_notations.

Import subalgebra_notations.

Section hom_inclusion_subalgebra.
  Context {σ} {A : Algebra σ} (P : SubalgebraPredicate A).

  Definition def_inclusion_subalgebra (s : Sort σ) : (A&P) s → A s
    := pr1.

  Lemma oppreserving_inclusion_subalgebra {w : SymbolType σ}
    (α : Operation A w) (C : ClosedUnderOp A P α)
    : OpPreserving def_inclusion_subalgebra (op_subalgebra P α C) α.
  Proof.
    induction w.
    - reflexivity.
    - intros x. apply IHw.
  Qed.

  Definition is_homomorphism_inclusion_subalgebra
    : IsHomomorphism def_inclusion_subalgebra.
  Proof.
    intro u. apply oppreserving_inclusion_subalgebra.
  Qed.

  Definition hom_inclusion_subalgebra : Homomorphism (A&P) A
    := BuildHomomorphism
        def_inclusion_subalgebra is_homomorphism_inclusion_subalgebra.

  Global Instance injection_inclusion_subalgebra
    : ∀ (s : Sort σ), Injective (hom_inclusion_subalgebra s).
  Proof.
    intros s x y p. by apply path_sigma_hprop.
  Qed.

  Lemma surjection_inclusion_subalgebra (full : ∀ s (x : A s), P s x)
    : ∀ (s : Sort σ), IsSurjection (hom_inclusion_subalgebra s).
  Proof.
    intros s.
    apply BuildIsSurjection.
    intro y.
    apply tr.
    by exists (y; full s y).
  Qed.

  Lemma is_isomorphism_inclusion_subalgebra (full : ∀ s (x : A s), P s x)
    : IsIsomorphism hom_inclusion_subalgebra.
  Proof.
    constructor.
    - exact _.
    - by apply surjection_inclusion_subalgebra.
  Qed.

  Lemma path_ap_operation_inclusion_subalgebra'
    {w : SymbolType σ} (a : FamilyProd (A&P) (dom_symboltype w))
    (α : Operation A w) (C : ClosedUnderOp A P α)
    : ap_operation α (map_family_prod hom_inclusion_subalgebra a)
      = hom_inclusion_subalgebra (cod_symboltype w)
          (ap_operation (op_subalgebra P α C) a).
  Proof.
    induction w.
    - reflexivity.
    - apply IHw.
  Defined.

  Lemma path_ap_operation_inclusion_subalgebra (u : Symbol σ)
    (a : FamilyProd (A&P) (dom_symboltype (σ u)))
    : ap_operation (u^^A) (map_family_prod hom_inclusion_subalgebra a)
      = hom_inclusion_subalgebra (cod_symboltype (σ u))
          (ap_operation (u ^^ A&P) a).
  Proof.
    apply path_ap_operation_inclusion_subalgebra'.
  Defined.
End hom_inclusion_subalgebra.
