Require Import
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Universe
  HoTT.HIT.quotient
  HoTT.Classes.interfaces.abstract_algebra
  HoTTClasses.interfaces.ua_algebra
  HoTTClasses.interfaces.ua_congruence
  HoTTClasses.theory.ua_homomorphism
  HoTTClasses.theory.ua_subalgebra
  HoTTClasses.theory.ua_quotient_algebra
  HoTTClasses.theory.ua_first_isomorphism.

Import algebra_notations quotient_algebra_notations subalgebra_notations.

Definition test {σ} {A B : Algebra σ}
  (g h : Homomorphism A B) (s : Sort σ) (x y : B s) : Type
  := ∀ (Ψ : Congruence B),
    (∀ (t : Sort σ) (a : A t), Ψ t (g t a) (h t a)) → Ψ s x y.

Global Instance meme `{Funext} {σ} {A B : Algebra σ} (g h : Homomorphism A B) (s : Sort σ)
  : is_mere_relation (B s) (test g h s).
Proof.
  intros.
  apply trunc_forall.
Defined.

Global Instance eqeq {σ} {A B : Algebra σ} (g h : Homomorphism A B)
  (s : Sort σ) : Equivalence (test g h s).
Proof.
  constructor.
  - unfold Reflexive.
    intros x Ψ ?. reflexivity. 
  - intros x y T Ψ ?. symmetry. apply T.
    apply X.
  - intros x y z. intros T1 T2.
    intros Ψ ?.
    transitivity y.
    apply T1.
    apply X.
    apply T2. apply X.
Defined.

Global Instance haha {σ} {A B : Algebra σ} (g h : Homomorphism A B)
  : HasCongruenceProperty B (test g h).
Proof.
  intro u.
  unfold CongruenceProperty.
  intros a b F Ψ G.
  apply (property_congruence Ψ u).
  induction (σ u).
  - simpl in *. auto.
  - simpl in *.
    split.
    + apply F. apply G.
    + apply IHs. apply F.
Defined.

Definition coco `{Funext} {σ} {A B : Algebra σ} (g h : Homomorphism A B)
  : Congruence B
  := BuildCongruence (test g h).

Definition himm {σ} {A B : Algebra σ} (f : Homomorphism A B) (s : Sort σ)
  : relation (A s)
  := λ x y, f s x = f s y.

Global Instance equ_himm
 {σ} {A B : Algebra σ} (f : Homomorphism A B) (s : Sort σ)
 : Equivalence (himm f s).
Proof.
  constructor.
  - intro x. reflexivity.
  - intros x y F. by symmetry.
  - intros x y z F1 F2. by transitivity y.
Defined.

Global Instance prpr_himm
 {σ} {A B : Algebra σ} (f : Homomorphism A B)
 : HasCongruenceProperty A (himm f).
Proof.
  intro u.
  intros a b F.
  unfold himm.
  rewrite path_homomorphism_ap_operation.
  rewrite path_homomorphism_ap_operation.
  set (bo := u^^B).
  clearbody bo.
  induction (σ u).
  - simpl. reflexivity.
  - simpl in *.
    destruct a as [x a], b as [y b].
    simpl in *.
    destruct F as [F1 F2].
    unfold himm in F1.
    simpl.
    rewrite F1.
    apply IHs.
    assumption.
Defined.

Definition himc
 {σ} {A B : Algebra σ} (f : Homomorphism A B)
 : Congruence A
 := BuildCongruence (himm f).

Lemma prop `{Funext} {σ} {A B C : Algebra σ} (g h : Homomorphism A B)
  (f : Homomorphism B C) (p : hom_compose f g = hom_compose f h)
  : ∀ s x y, test g h s x y → f s x = f s y.
Proof.
  intros.
  specialize (X (himc f)).
  apply X.
  intros t a.
  unfold himc.
  simpl.
  unfold himm.
  change (f t (g t a)) with (hom_compose f g t a).
  rewrite p.
  reflexivity.
Defined.
