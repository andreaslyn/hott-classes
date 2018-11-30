Require Import
  Coq.Unicode.Utf8
  HoTTClasses.implementations.ne_list
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_basic
  HoTT.Basics.Equivalences
  HoTT.Types.Forall
  HoTT.HSet
  HoTT.Types.Universe
  HoTT.Basics.PathGroupoids
  HoTT.Tactics.

Import nel.notations.
Import algebra_notations.

(* TODO Put this next to Injective and rename Injective. *)
Class IsSetSurjection {A B : Type} (f : A → B) : Type :=
  is_set_surjection : ∀ (y:B), hfiber f y.

Section ishomomorphism.
  Context {σ : Signature} {A B : Algebra σ} (f : ∀ s, A s → B s).

  Fixpoint OpPreserving {n : opsym_type σ}
    : op_type A n → op_type B n → Type
    := match n with
       | [:d:] => λ oA oB, f d oA = oB
       | d ::: y => λ oA oB, ∀ x, OpPreserving (oA x) (oB (f d x))
       end.

  Global Instance hprop_op_preservation {Fu : Funext} {n : opsym_type σ}
    (a : op_type A n) (b : op_type B n)
    : IsHProp (OpPreserving a b).
  Proof.
    intros. induction n; apply _.
  Defined.

  Class IsHomomorphism : Type :=
    op_preserving : ∀ (u : sigsym σ), OpPreserving (u^^A) (u^^B).

  Global Instance hprop_ishomomorphism {Fu : Funext} : IsHProp IsHomomorphism.
  Proof.
    intros. apply trunc_forall.
  Defined.

  Class IsIsomorphism `{Ho : IsHomomorphism} : Type :=
    { setinjection_iso : ∀ (s : sigsort σ), Injective (f s)
    ; setsurjection_iso : ∀ (s : sigsort σ), IsSetSurjection (f s) }.

  Global Existing Instance setinjection_iso.
  Global Existing Instance setsurjection_iso.
End ishomomorphism.

Record Homomorphism {σ} (A B : Algebra σ) : Type := BuildHomomorphism
  { hom_map : ∀ s, A s → B s
  ; ishomomorphism_hom : IsHomomorphism hom_map }.

Global Coercion hom_map : Homomorphism >-> Funclass.
Global Existing Instance ishomomorphism_hom.

Global Hint Unfold hom_map : typeclass_instances.

Arguments BuildHomomorphism {σ} {A} {B} hom_map {ishomomorphism_hom}.

Global Instance isequiv_forgetful_iso {σ} {A B : Algebra σ}
    (f : Homomorphism A B) {Is : IsIsomorphism f}
    : ∀ s, IsEquiv (f s).
Proof.
  intro s. apply isequiv_surj_emb.
  - apply BuildIsSurjection. intro y. apply tr. apply Is.
  - apply isembedding_isinj_hset. apply Is.
Defined.

Definition equiv_forgetful_iso {σ} {A B : Algebra σ}
    (f : Homomorphism A B) {Is : IsIsomorphism f}
    : ∀ s, A s <~> B s.
Proof.
  intro s. rapply (BuildEquiv _ _ (f s)).
Defined.

Global Instance ishomomorphism_hom_id {σ} (A : Algebra σ)
  : IsHomomorphism (λ _, idmap).
Proof.
 intro u. generalize (u^^A). intro w. induction (σ u).
 - reflexivity.
 - now intro x.
Qed.

Global Instance isisomorphism_hom_id {σ} (A : Algebra σ)
  : IsIsomorphism (λ _, idmap).
Proof.
  constructor; intro s.
  - intros x y. exact idmap.
  - intro y. exact (y; idpath).
Qed.

Definition hom_id {σ} {A : Algebra σ} : Homomorphism A A
  := BuildHomomorphism (λ _, idmap).

Global Instance ishomomorphism_hom_inv {σ} (A B : Algebra σ)
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsHomomorphism (λ s, (f s)^-1).
Proof.
 intro u.
 generalize (u^^A) (u^^B) (op_preserving f u).
 intros a b P.
 induction (σ u).
 - rewrite <- P. apply (eissect (f t)).
 - intro. apply IHo.
   exact (
    transport (λ y, OpPreserving f _ (b y)) (eisretr (f t) x) (P (_^-1 x))).
Qed.

Global Instance isisomorphism_hom_inv {σ} (A B : Algebra σ)
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsIsomorphism (λ s, (f s)^-1).
Proof.
  constructor.
  - intros s x y p.
    now rewrite <- (eisretr (f s) x), <- (eisretr (f s) y), p.
  - intros s y. exists (f s y). apply (eissect (f s) y).
Qed.

Definition hom_inv {σ} {A B : Algebra σ} (f : Homomorphism A B)
    `{!IsIsomorphism f}
    : Homomorphism B A
  := BuildHomomorphism (λ s, (f s)^-1).

Lemma oppreserving_hom_compose {σ} {A B C : Algebra σ} {w : opsym_type σ}
  {a : op_type A w} {b : op_type B w} {c : op_type C w}
  (g : Homomorphism B C) (f : Homomorphism A B)
  (G : OpPreserving g b c) (F : OpPreserving f a b)
  : OpPreserving (λ s (x : A s), g s (f s x)) a c.
Proof.
 induction w; simpl.
 - now rewrite F, G.
 - intro x. now apply (IHw _ (b (f _ x))).
Qed.

Global Instance ishomomorphism_hom_compose {σ} {A B C : Algebra σ}
  (g : Homomorphism B C) (f : Homomorphism A B)
  : IsHomomorphism (λ s, g s ∘ f s).
Proof.
 intro u.
 exact (oppreserving_hom_compose g f (op_preserving g u) (op_preserving f u)).
Qed.

Definition hom_compose {σ} {A B C : Algebra σ}
    (g : Homomorphism B C) (f : Homomorphism A B)
    : Homomorphism A C
  := BuildHomomorphism (λ s, g s ∘ f s).

Global Instance isisomorphism_hom_compose {σ} {A B C : Algebra σ}
  (g : Homomorphism B C) `{!IsIsomorphism g}
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : IsIsomorphism (λ s, g s ∘ f s).
Proof.
 constructor.
 - intros s x y p.
   apply (setinjection_iso f).
   by apply (setinjection_iso g).
 - intros s z. exists ((f s)^-1 ((g s)^-1 z)).
   unfold Compose. by rewrite (eisretr (f s)), (eisretr (g s)).
Qed.

Definition path_equiv_carriers `{Univalence} {σ} {A B : Algebra σ}
  (f : ∀ (s : sigsort σ), A s <~> B s)
  : carriers A = carriers B
  := path_forall A B (λ s : sigsort σ, path_universe (f s)).

Lemma path_transport_carriers_equiv `{Univalence} {σ} {A B : Algebra σ}
  {w : opsym_type σ} (f : ∀ (s : sigsort σ), A s <~> B s)
  (ao : op_type A w) (bo : op_type B w) (P : OpPreserving f ao bo)
  : transport (λ s : Carriers σ, op_type s w)
      (path_equiv_carriers f) ao = bo.
Proof.
  unfold path_equiv_carriers.
  induction w; simpl in *.
  transport_path_forall_hammer.
  rewrite <- P.
  by rewrite transport_idmap_path_universe.
  funext y.
  specialize (P ((f t)^-1 y)).
  rewrite (eisretr (f t)) in P.
  transport_path_forall_hammer.
  rewrite transport_forall_constant.
  rewrite transport_forall.
  rewrite transport_const.
  rewrite (transport_path_universe_V (f t)).
  destruct (path_universe (f t)).
  exact (IHw (ao ((f t)^-1 y)) (bo y) P).
Qed.

Lemma path_transport_carriers_isomorphism `{Univalence} {σ} {A B : Algebra σ}
  (f : Homomorphism A B) `{!IsIsomorphism f} (u : sigsym σ)
  : transport (λ s : Carriers σ, op_type s (σ u))
      (path_equiv_carriers (equiv_forgetful_iso f)) (u^^A)
    = u^^B.
Proof.
  apply path_transport_carriers_equiv. apply (op_preserving f).
Defined.

Theorem path_isomorphism `{Univalence} {σ} {A B : Algebra σ}
  (f : Homomorphism A B) `{!IsIsomorphism f}
  : A = B.
Proof.
  apply path_sig_path_algebra_algebra.
  exists (path_equiv_carriers (equiv_forgetful_iso f)).
  funext u.
  refine (transport (λ x : op_type B (σ u), x = u^^B)
            (transport_forall_constant _ _ u)^
            (path_transport_carriers_isomorphism f u)).
Defined.

Corollary iff_path_isomorphism `{Univalence} {σ} {A B : Algebra σ}
  : (∃ (f : Homomorphism A B), IsIsomorphism f) ↔ A = B.
Proof.
  split.
  - intros [f Is]. apply (path_isomorphism f).
  - intros p. path_induction. exists hom_id. apply _.
Defined.
