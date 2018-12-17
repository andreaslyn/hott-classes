(** This file implements algebra [Homomorphism] and [IsIsomorphism].
    It developes basic algebra homomorphisms and isomorphims. The main
    theorem in this file is the [path_isomorphism] theorem, which
    states that there is a path between isomorphic algebras. *)

Require Import
  HoTT.Basics.Equivalences
  HoTT.Basics.PathGroupoids
  HoTT.Types.Forall
  HoTT.Types.Arrow
  HoTT.Types.Universe
  HoTT.Types.Record
  HoTT.Types.Sigma
  HoTT.HSet
  HoTT.Tactics
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra.

Import algebra_notations ne_list.notations.

Section is_homomorphism.
  Context {σ} {A B : Algebra σ} (f : ∀ (s : Sort σ), A s → B s).

(** The family of functions [f] above is [OpPreserving α β] with
    respect to operations [α : A s1 → A s2 → ... → A sn → A t] and
    [β : B s1 → B s2 → ... → B sn → B t] if

    <<
      f t (α x1 x2 ... xn) = β (f s1 x1) (f s2 x2) ... (f sn xn)
    >>
*)

  Fixpoint OpPreserving {w : SymbolType σ}
    : Operation A w → Operation B w → Type
    := match w with
       | [:s:] => λ α β, f s α = β
       | s ::: y => λ α β, ∀ (x : A s), OpPreserving (α x) (β (f s x))
       end.

  Global Instance hprop_oppreserving `{Funext} {w : SymbolType σ}
    (α : Operation A w) (β : Operation B w)
    : IsHProp (OpPreserving α β).
  Proof.
    intros. induction w; exact _.
  Defined.

(** The family of functions [f : ∀ (s : Sort σ), A s → B s] above is
    a homomorphism if for each function symbol [u : Symbol σ], it is
    [OpPreserving (u^^A) (u^^B)] with respect to the algebra
    operations [u^^A] and [u^^B] corresponding to [u]. *)

  Class IsHomomorphism : Type :=
    op_preserving : ∀ (u : Symbol σ), OpPreserving (u^^A) (u^^B).

  Global Instance hprop_is_homomorphism `{Funext}
    : IsHProp IsHomomorphism.
  Proof.
    intros. apply trunc_forall.
  Defined.
End is_homomorphism.

(** Gival algebras [A B : Algebra σ] a homomorphism [Homomorphism A B]
    is a family of functions [f : ∀ (s : Sort σ), A s → B s] where
    [IsHomomorphism f] holds. *)

Record Homomorphism {σ} {A B : Algebra σ} : Type := BuildHomomorphism
  { def_hom : ∀ (s : Sort σ), A s → B s
  ; is_homomorphism_hom : IsHomomorphism def_hom }.

Arguments Homomorphism {σ} A B.

Arguments BuildHomomorphism {σ A B} def_hom {is_homomorphism_hom}.

(** We the implicit coercion from [Homomorphism A B] to the family
    of functions [∀ s, A s → B s]. *)

Global Coercion def_hom : Homomorphism >-> Funclass.

Global Existing Instance is_homomorphism_hom.

Definition SigHomomorphism {σ} (A B : Algebra σ) : Type :=
  {def_hom : ∀ s, A s → B s | IsHomomorphism def_hom}.

Lemma issig_homomorphism {σ} (A B : Algebra σ)
  : Homomorphism A B <~> SigHomomorphism A B.
Proof.
  apply symmetric_equiv.
  unfold SigHomomorphism.
  issig (@BuildHomomorphism σ A B) (@def_hom σ A B)
    (@is_homomorphism_hom σ A B).
Defined.

(** To find a path between homomorphisms [f g : Homomorphism A B],
    it suffices to find a path between the defining families of
    functions. *)

Lemma path_homomorphism `{Funext} {σ} {A B : Algebra σ}
  (f g : Homomorphism A B) (p : ∀ s, f s == g s) : f = g.
Proof.
  transparent assert (F : (def_hom f = def_hom g)).
  - funext s x. apply p.
  - apply (ap (issig_homomorphism A B))^-1. by apply path_sigma_hprop.
Defined.

(** [f : Homomorphism A B] is an isomorphism if for each [s : Sort σ],
    [f s] is both injective and surjective. *)

Class IsIsomorphism {σ : Signature} {A B : Algebra σ}
  (f : Homomorphism A B) : Type
  := BuildIsIsomorphism
    { injection_isomorphism : ∀ (s : Sort σ), Injective (f s)
    ; surjection_isomorphism : ∀ (s : Sort σ), IsSurjection (f s) }.

Global Existing Instance injection_isomorphism.

Global Existing Instance surjection_isomorphism.

Definition SigIsIsomorphism {σ} {A B : Algebra σ}
  (f : Homomorphism A B) : Type
  := { injection_isomorphism : ∀ (s : Sort σ), Injective (f s)
     | ∀ (s : Sort σ), IsSurjection (f s) }.

Lemma issig_is_isomorphism {σ : Signature} {A B : Algebra σ}
  (f : Homomorphism A B)
  : IsIsomorphism f <~> SigIsIsomorphism f.
Proof.
  apply symmetric_equiv.
  unfold SigIsIsomorphism.
  issig (@BuildIsIsomorphism σ A B f) (@injection_isomorphism σ A B f)
    (@surjection_isomorphism σ A B f).
Defined.

Global Instance hprop_is_isomorphism `{Funext} {σ} {A B : Algebra σ}
  (f : Homomorphism A B)
  : IsHProp (IsIsomorphism f).
Proof.
  apply HProp.equiv_hprop_allpath.
  intros i j.
  apply (ap (issig_is_isomorphism f))^-1.
  apply path_sigma_hprop.
  funext s x y p.
  apply set_path2.
Defined.

(** Suppose [f : Homomorphism A B] and [f s] is injective for all [s :
    Sort σ]. Then [f s] is an embedding for all [s : Sort σ]. *)

Global Instance embedding_homomorphism {σ} {A B : Algebra σ}
  (f : Homomorphism A B) {In : ∀ s, Injective (f s)}
  : ∀ s, IsEmbedding (f s).
Proof.
  intro s. apply isembedding_isinj_hset. apply In.
Defined.

(** The following section shows that an isomorphism between algebras
    [A B : Algebra σ] induces a family of equivalences between the
    carriers,

    <<
      ∀ (s : Sort σ), A s <~> B s
    >>
*)

Section equiv_carriers_isomorphism.
  Context
    {σ : Signature}
    {A B : Algebra σ}
    (f : Homomorphism A B)
    {Is : IsIsomorphism f}.

  Global Instance isequiv_carriers_isomorphism
    : ∀ (s : Sort σ), IsEquiv (f s).
  Proof.
    intro s. apply isequiv_surj_emb; exact _.
  Defined.

  Definition equiv_carriers_isomorphism : ∀ (s : Sort σ), A s <~> B s.
  Proof.
    intro s. rapply (BuildEquiv _ _ (f s)).
  Defined.
End equiv_carriers_isomorphism.

(** Let [f : Homomorphism A B] be a homomorphism. The following
    section proves that [f] is "OpPreserving" with respect to
    uncurried algebra operations in the sense that

    <<
      f t (α (x1,x2,...,xn,tt)) = β (f s1 x1,f s2 x1,...,f sn xn,tt)
    >>

    for all [(x1,x2,...,xn,tt) : FamilyProd A [s1;s2;...;sn]], where
    [α] and [β] are uncurried algebra operations in [A] and [B]
    respectively.
*)

Section homomorphism_ap_operation.
  Context {σ : Signature} {A B : Algebra σ} (f : Homomorphism A B).

  Lemma path_homomorphism_ap_operation' {w : SymbolType σ}
    (a : FamilyProd A (dom_symboltype w)) (α : Operation A w)
    (β : Operation B w) (P : OpPreserving f α β)
    : f (cod_symboltype w) (ap_operation α a) =
      ap_operation β (map_family_prod f a).
  Proof.
    induction w.
    - assumption.
    - destruct a as [x a]. apply IHw. apply P.
  Defined.

  Lemma path_homomorphism_ap_operation
    : ∀ (u : Symbol σ) (a : FamilyProd A (dom_symboltype (σ u))),
      f (cod_symboltype (σ u)) (ap_operation (u^^A) a)
      = ap_operation (u^^B) (map_family_prod f a).
  Proof.
    intros u a.
    apply path_homomorphism_ap_operation'.
    apply f.
  Defined.
End homomorphism_ap_operation.

(** The next section shows that the family of identity functions,
    [f s x = x] is an isomorphism. *)

Section hom_id.
  Context {σ} (A : Algebra σ).

  Global Instance is_homomorphism_id
    : @IsHomomorphism σ A A (λ _, idmap).
  Proof.
   intro u. generalize (u^^A). intro w. induction (σ u).
   - reflexivity.
   - now intro x.
  Qed.

  Definition hom_id : Homomorphism A A
    := BuildHomomorphism (λ _, idmap).

  Global Instance is_isomorphism_id : IsIsomorphism hom_id.
  Proof.
    constructor; intro s.
    - intros x y. exact idmap.
    - apply BuildIsSurjection. intro y. exact (tr (y; idpath)).
  Qed.
End hom_id.

(** Suppose [f : Homomorphism A B] and [IsIsomorphism f]. The next
    section provides an inverse homomorphism [g : Homomorphism B A],
    which is also an isomorphism [IsIsomorphism g]. The homomorphism
    [g] satisfies [g s (f s x) = x] for all [s : Sort σ]. *)

Section hom_inv.
  Context {σ} {A B : Algebra σ}.

  Global Instance is_homomorphism_inv (f : Homomorphism A B)
    `{!IsIsomorphism f}
    : IsHomomorphism (λ s, (f s)^-1).
  Proof.
   intro u.
   generalize (u^^A) (u^^B) (op_preserving f u).
   intros a b P.
   induction (σ u).
   - rewrite <- P. apply (eissect (f t)).
   - intro. apply IHs.
     exact (transport (λ y, OpPreserving f _ (b y))
              (eisretr (f t) x) (P (_^-1 x))).
  Qed.

  Definition hom_inv (f : Homomorphism A B) `{!IsIsomorphism f}
    : Homomorphism B A
    := BuildHomomorphism (λ s, (f s)^-1).

  Global Instance is_isomorphism_inv (f : Homomorphism A B)
    `{!IsIsomorphism f}
    : IsIsomorphism (hom_inv f).
  Proof.
    constructor.
    - intros s x y p.
      rewrite <- (eisretr (f s) x), <- (eisretr (f s) y).
      auto.
    - intro s.
      apply BuildIsSurjection.
      intro y.
      apply tr.
      exists (f s y).
      apply (eissect (f s) y).
  Qed.
End hom_inv.

(** Let [f : Homomorphism A B] and [g : Homomorphism B C]. The
    following section shows that composition given by [λ (s : Sort σ),
    g s ∘ f s] is again a homomorphism. If both [f] and [g] are
    isomorphisms, then the composition is an isomorphism. *)

Section hom_compose.
  Context {σ} {A B C : Algebra σ}.

  Lemma oppreserving_compose {w : SymbolType σ}
    {α : Operation A w} {β : Operation B w} {γ : Operation C w}
    (g : Homomorphism B C) (f : Homomorphism A B)
    (G : OpPreserving g β γ) (F : OpPreserving f α β)
    : OpPreserving (λ s (x : A s), g s (f s x)) α γ.
  Proof.
   induction w; simpl.
   - now rewrite F, G.
   - intro x. now apply (IHw _ (β (f _ x))).
  Qed.

  Global Instance is_homomorphism_compose (g : Homomorphism B C)
    (f : Homomorphism A B)
    : IsHomomorphism (λ s, g s ∘ f s).
  Proof.
   intro u.
   exact (oppreserving_compose g f
            (op_preserving g u) (op_preserving f u)).
  Qed.

  Definition hom_compose (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
    := BuildHomomorphism (λ s, g s ∘ f s).

  Global Instance is_isomorphism_compose
    (g : Homomorphism B C) `{!IsIsomorphism g}
    (f : Homomorphism A B) `{!IsIsomorphism f}
    : IsIsomorphism (hom_compose g f).
  Proof.
   constructor.
   - intros s x y p.
     by do 2 apply injection_isomorphism.
   - intro s.
     apply BuildIsSurjection.
     intro z.
     apply tr.
     exists ((f s)^-1 ((g s)^-1 z)).
     unfold hom_compose, def_hom, Compose.
     by rewrite (eisretr (f s)), (eisretr (g s)).
  Qed.
End hom_compose.

Lemma path_forall_recr_beta `{Funext} {A : Type} {B : A → Type}
  (a : A) (P : (∀ x, B x) → B a → Type) (f g : ∀ a, B a)
  (e : f == g) (Pa : P f (f a))
  : transport (fun f => P f (f a)) (path_forall f g e) Pa
    = transport (fun x => P x (g a))
        (path_forall f g e) (transport (fun y => P f y) (e a) Pa).
Proof.
  rewrite <- (eissect (path_forall f g) e).
  change ((_^-1 (path_forall f g e))) with ((apD10 (path_forall f g e))).
  destruct (path_forall f g e).
  unfold apD10.
  rewrite (path_forall_1 f).
  reflexivity.
Defined.

(** The following section proves that there is a path between
    isomorphic algebras. *)

Section path_isomorphism.
  Context `{Univalence} {σ : Signature} {A B : Algebra σ}.

(** Recall that there is an implicit coercion

    <<
      Coercion carriers : Algebra >-> Funclass
    >>

    so that [A s] is notation for [carriers A s]. *)

(** If [f : ∀ (s : Sort σ), A s <~> B s] is a family of equivalences,
    then by function extensionality and univalence there is a path
    between the carriers, [carriers A = carriers B]. *)

  Definition path_carriers_equiv {I : Type} {X Y : I → Type} (f : ∀ i, X i <~> Y i)
    : X = Y
    := path_forall X Y (λ i, path_universe (f i)).

(** Given a family of equivalences [f : ∀ (s : Sort σ), A s <~> B s]
    which is [OpPreserving f α β] with respect to algebra operations

    <<
      α : A s1 → A s2 → ... → A sn → A t
      β : B s1 → B s2 → ... → B sn → B t
    >>

    By transporting [α] along the path [path_carriers_equiv f] we
    find a path from the transported operation [α] to [β]. *)

  Lemma path_operations_equiv (f : ∀ (s : Sort σ), A s <~> B s)
    {w : SymbolType σ} (α : Operation A w) (β : Operation B w)
    (P : OpPreserving f α β)
    : transport (λ C : Carriers σ, Operation C w)
        (path_carriers_equiv f) α = β.
  Proof.
    unfold path_carriers_equiv.
    induction w; simpl in *.
    - rewrite (path_forall_recr_beta t (λ _ x, x) A B (λ s, path_universe (f s)) α).
      induction (path_forall A B (λ s : Sort σ, path_universe (f s))).
      (* transport_path_forall_hammer. *)

      exact (ap10 (transport_idmap_path_universe (f t)) α @ P).
    - funext y.

      set (Λ := λ (a : Sort σ → Type) (b:Type), b → Operation a w).
      rewrite (path_forall_recr_beta t Λ A B (λ s, path_universe (f s)) α).
      (*transport_path_forall_hammer.*)
      
      rewrite transport_forall_constant.
      rewrite transport_arrow_toconst.
      rewrite (transport_path_universe_V (f t)).
      specialize (P ((f t)^-1 y)).
      rewrite (eisretr (f t)) in P.
      exact (IHw (α ((f t)^-1 y)) (β y) P).
  Qed.

(** Suppose [u : Symbol σ] is a function symbol. Recall that
    [u^^A] is notation for [operations A u : Operation A (σ u)]. This
    is the algebra operation corresponding to function symbol [u]. *)

(** An isomorphism [f : Homomorphism A B] induces a family of
    equivalences [e : ∀ (s : Sort σ), A s <~> B s]. Let [u : Symbol σ]
    be a function symbol. Since [f] is a homomorphism, the induced
    family of equivalences [e] satisfies [OpPreserving e (u^^A) (u^^B)].
    By [path_operations_equiv] above, we can then transport [u^^A] along
    the path [path_carriers_equiv e] and obtain a path to [u^^B]. *)

  Lemma path_operations_isomorphism (f : Homomorphism A B)
    `{!IsIsomorphism f} (u : Symbol σ)
    : transport (λ C : Carriers σ, Operation C (σ u))
        (path_carriers_equiv (equiv_carriers_isomorphism f)) (u^^A)
      = u^^B.
  Proof.
    apply path_operations_equiv. apply (op_preserving f).
  Defined.

(** If there is an isomorphism [Homomorphism A B] then [A = B]. *)

  Theorem path_isomorphism (f : Homomorphism A B) `{!IsIsomorphism f}
    : A = B.
  Proof.
    apply path_algebra.
    exists (path_carriers_equiv (equiv_carriers_isomorphism f)).
    funext u.
    exact (transport_forall_constant _ _ u
           @ path_operations_isomorphism f u).
  Defined.
End path_isomorphism.
