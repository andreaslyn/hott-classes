Require Import
  Coq.Unicode.Utf8
  HoTT.Classes.interfaces.canonical_names.

Require Export HoTT.Classes.interfaces.abstract_algebra.

Section jections.
  Context {A B} (f : A → B) `{inv : !Inverse f}.

  Class Surjective : Type :=
    { surjective : f ∘ (f ⁻¹) = id (* a.k.a. "split-epi" *) }.

  Class Bijective : Type :=
    { bijective_injective :> Injective f
    ; bijective_surjective :> Surjective }.
End jections.

Section morphism_classes.
  Context {A B : Type}.

  Class SemiGroup_Morphism {Aop Bop} (f : A → B) :=
    { sgmor_a : @SemiGroup A Aop
    ; sgmor_b : @SemiGroup B Bop
    ; preserves_sg_op : ∀ x y, f (x & y) = f x & f y }.

  Class JoinSemiLattice_Morphism {Ajoin Bjoin} (f : A → B) :=
    { join_slmor_a : @JoinSemiLattice A Ajoin
    ; join_slmor_b : @JoinSemiLattice B Bjoin
    ; join_slmor_sgmor :> @SemiGroup_Morphism join_is_sg_op join_is_sg_op f }.

  Class MeetSemiLattice_Morphism {Ameet Bmeet} (f : A → B) :=
    { meet_slmor_a : @MeetSemiLattice A Ameet
    ; meet_slmor_b : @MeetSemiLattice B Bmeet
    ; meet_slmor_sgmor :> @SemiGroup_Morphism meet_is_sg_op meet_is_sg_op f }.

  Class Monoid_Morphism {Aunit Bunit Aop Bop} (f : A → B) :=
    { monmor_a : @Monoid A Aop Aunit
    ; monmor_b : @Monoid B Bop Bunit
    ; monmor_sgmor :> SemiGroup_Morphism f
    ; preserves_mon_unit : f mon_unit = mon_unit }.

  Class BoundedJoinSemiLattice_Morphism {Abottom Bbottom Ajoin Bjoin} (f : A → B) :=
    { bounded_join_slmor_a : @BoundedJoinSemiLattice A Ajoin Abottom
    ; bounded_join_slmor_b : @BoundedJoinSemiLattice B Bjoin Bbottom
    ; bounded_join_slmor_monmor :> @Monoid_Morphism bottom_is_mon_unit bottom_is_mon_unit join_is_sg_op join_is_sg_op f }.

  Class SemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f : A → B) :=
    { semiringmor_a : @SemiRing A Aplus Amult Azero Aone
    ; semiringmor_b : @SemiRing B Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor :> @Monoid_Morphism zero_is_mon_unit zero_is_mon_unit plus_is_sg_op plus_is_sg_op f
    ; semiringmor_mult_mor :> @Monoid_Morphism one_is_mon_unit one_is_mon_unit mult_is_sg_op mult_is_sg_op f }.

  Class Lattice_Morphism {Ajoin Ameet Bjoin Bmeet} (f : A → B) :=
    { latticemor_a : @Lattice A Ajoin Ameet
    ; latticemor_b : @Lattice B Bjoin Bmeet
    ; latticemor_join_mor :> JoinSemiLattice_Morphism f
    ; latticemor_meet_mor :> MeetSemiLattice_Morphism f }.
End morphism_classes.
