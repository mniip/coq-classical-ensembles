Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FinFun.

Require Import ClassicalEnsembles.Core.
Require Import ClassicalEnsembles.Tactics.
Require Import ClassicalEnsembles.Algebra.
Require Import ClassicalEnsembles.Families.

Import SetElementNotation.
Import SetAlgebraNotation.
Import SetFamilyNotation.

Inductive Image {X Y} (f : X -> Y) : Ensemble Y
  := Image_intro : forall x, f x ∈ Image f.
Inductive DirectImage {X Y} (f : X -> Y) (A : Ensemble X) : Ensemble Y
  := DirectImage_intro : forall x, x ∈ A -> f x ∈ DirectImage f A.
Inductive Preimage {X Y} (f : X -> Y) (A : Ensemble Y) : Ensemble X
  := Preimage_intro : forall x, f x ∈ A -> x ∈ Preimage f A.

Module SetImageNotation.

Notation "f '¹'" := (DirectImage f)
  (at level 0).
Notation "f '⁻¹'" := (Preimage f)
  (at level 0).

End SetImageNotation.
Import SetImageNotation.

Theorem image_char {X Y} {f : X -> Y} y
  : y ∈ Image f = exists x, y = f x.
Proof.
  apply propositional_extensionality. split.
  - intros []. eauto.
  - intros [? ->]. constructor.
Qed.

Theorem direct_image_char {X Y} {f : X -> Y} {A : Ensemble X} y
  : y ∈ f¹ A = exists x, x ∈ A /\ y = f x.
Proof.
  apply propositional_extensionality. split.
  - intros []. eauto.
  - intros [? [? ->]]. now constructor.
Qed.

Theorem preimage_char {X Y} {f : X -> Y} {A : Ensemble Y} x
  : x ∈ f⁻¹ A = f x ∈ A.
Proof.
  apply propositional_extensionality. split.
  - intros []. auto.
  - now constructor.
Qed.

Global Hint Resolve Image_intro DirectImage_intro Preimage_intro : sets.
Global Hint Rewrite @image_char : sets.
Global Hint Rewrite @direct_image_char : sets.
Global Hint Rewrite @preimage_char : sets.

Theorem image_surj {X Y} (f : X -> Y)
  : Surjective f -> Image f = ⊤.
Proof.
  unfold Surjective. intros p.
  setext. unset. split; auto.
  intros y _. destruct (p y) as [x]. now exists x.
Qed.

Theorem image_identity {X}
  : Image (fun x => x) = ⊤ :> Ensemble X.
Proof. setsolve. Qed.

Theorem image_composition {X Y Z} (f : Y -> Z) (g : X -> Y)
  : Image (fun x => f (g x)) = f¹(Image g).
Proof.
  setext. unset. split.
  - intros ? [x ->]. exists (g x). split; auto. now exists x.
  - intros ? [? [[x ->] ->]]. now exists x.
Qed.

Theorem direct_image_subset_image {X Y} (f : X -> Y) (A : Ensemble X)
  : f¹ A ⊂ Image f.
Proof. setsolve_firstorder. Qed.

Theorem direct_image_empty {X Y} (f : X -> Y)
  : f¹ ∅ = ∅.
Proof. setsolve_firstorder. Qed.

Theorem direct_image_full {X Y} (f : X -> Y)
  : f¹ ⊤ = Image f.
Proof. setsolve_firstorder. Qed.

Theorem direct_image_full_surj {X Y} (f : X -> Y)
  : Surjective f -> f¹ ⊤ = ⊤.
Proof.
  unfold Surjective. intros s.
  setext. unset. split; auto.
  intros y _. destruct (s y) as [x]. now exists x.
Qed.

Theorem direct_image_complement {X Y} (f : X -> Y) (A : Ensemble X)
  : Image f ∩ (f¹ A)ᶜ ⊂ f¹(A ᶜ).
Proof. setsolve_firstorder. Qed.

Theorem direct_image_complement_inj {X Y} (f : X -> Y) (A : Ensemble X)
  : Injective f -> Image f ∩ (f¹ A)ᶜ = f¹(A ᶜ).
Proof.
  unfold Injective. intros i.
  setext. unset. split.
  - firstorder.
  - intros ? [x [j ->]]. split.
    + now exists x.
    + intros [x' []].
      contradiction j.
      erewrite i; eauto.
Qed.

Theorem direct_image_complement_surj {X Y} (f : X -> Y) (A : Ensemble X)
  : Surjective f -> (f¹ A)ᶜ ⊂ f¹(A ᶜ).
Proof.
  unfold Surjective. intros s.
  unset.
  intros y ne. destruct (s y) as [x <-].
  exists x. split; auto.
  intros ?. contradiction ne. now exists x.
Qed.

Theorem direct_image_complement_inj_surj {X Y} (f : X -> Y) (A : Ensemble X)
  : Injective f -> Surjective f -> (f¹ A)ᶜ = f¹(A ᶜ).
Proof.
  unfold Injective, Surjective. intros i s.
  setext. unset. split.
  - intros y ne. destruct (s y) as [x <-].
    exists x. split; auto.
    intros ?. contradiction ne. now exists x.
  - intros ? [x [j ->]] [x' []].
    contradiction j.
    erewrite i; eauto.
Qed.

Theorem direct_image_intersection {X Y} (f : X -> Y) (A B : Ensemble X)
  : f¹(A ∩ B) ⊂ f¹ A ∩ f¹ B.
Proof. setsolve_firstorder. Qed.

Theorem direct_image_intersection_inj {X Y} (f : X -> Y) (A B : Ensemble X)
  : Injective f -> f¹(A ∩ B) = f¹ A ∩ f¹ B.
Proof.
  unfold Injective. intros i.
  setext. split.
  - setsolve_firstorder.
  - unset. intros y [[x [? ->]] [x' []]].
    exists x'. split; auto.
    erewrite i in *; eauto.
Qed.

Theorem direct_image_union {X Y} (f : X -> Y) (A B : Ensemble X)
  : f¹(A ∪ B) = f¹ A ∪ f¹ B.
Proof. setsolve_firstorder. Qed.

Theorem direct_image_family_intersection {X Y I} (f : X -> Y) (F : I -> Ensemble X)
  : f¹(FamilyIntersection F) ⊂ ⋂i => f¹(F i).
Proof. setsolve_firstorder. Qed.

Theorem direct_image_family_intersection_inj {X Y I} (f : X -> Y) (F : I -> Ensemble X)
  : Injective f -> f¹(FamilyIntersection F) = Image f ∩ ⋂i => f¹(F i).
Proof.
  unfold Injective. intros i.
  setext. split.
  - setsolve_firstorder.
  - unset. intros ? [[x ->] j].
    exists x. split; auto.
    intros k. destruct (j k) as [x' []].
    erewrite i; eauto.
Qed.

Theorem direct_image_family_intersection_inj_surj {X Y I} (f : X -> Y) (F : I -> Ensemble X)
  : Injective f -> Surjective f -> f¹(FamilyIntersection F) = ⋂i => f¹(F i).
Proof.
  unfold Injective, Surjective. intros i s.
  setext. split.
  - setsolve_firstorder.
  - unset. intros y j.
    destruct (s y) as [x <-].
    exists x. split; auto.
    intros k. destruct (j k) as [x' []].
    erewrite i; eauto.
Qed.

Theorem direct_image_family_union {X Y I} (f : X -> Y) (F : I -> Ensemble X)
  : f¹(FamilyUnion F) = ⋃i => f¹(F i).
Proof. setsolve_firstorder. Qed.

Theorem direct_image_set_intersection {X Y} (f : X -> Y) (F : Ensemble (Ensemble X))
  : f¹(∩F) ⊂ ∩(f¹¹ F).
Proof. setsolve_firstorder. Qed.

Theorem direct_image_set_intersection_inj {X Y} (f : X -> Y) (F : Ensemble (Ensemble X))
  : Injective f -> f¹(∩F) = Image f ∩ ∩(f¹¹ F).
Proof.
  unfold Injective. intros i.
  setext. split.
  - setsolve_firstorder.
  - unset. intros ? [[x ->] j].
    exists x. split; auto. intros A ?.
    assert (f x ∈ f¹ A) as p.
    {
      apply j. now exists A.
    }
    unset. destruct p as [x' []].
    erewrite i; eauto.
Qed.

Theorem direct_image_set_union {X Y} (f : X -> Y) (F : Ensemble (Ensemble X))
  : f¹(∪F) = ∪(f¹¹ F).
Proof.
  setext. unset. split.
  - intros ? [x [[A []] ->]].
    exists (f¹ A). eauto with sets.
  - intros ? [? [[A [? ->]] [x]]].
    exists x; eauto.
Qed.

Theorem direct_image_mono {X Y} (f : X -> Y) (A B : Ensemble X)
  : A ⊂ B -> f¹ A ⊂ f¹ B.
Proof. setsolve_firstorder. Qed.

Theorem direct_image_identity {X} (A : Ensemble X)
  : (fun x => x)¹ A = A.
Proof.
  setext. unset. split.
  - now intros ? [x [? ->]].
  - intros x ?. now exists x.
Qed.

Theorem direct_image_composition {X Y Z} (f : Y -> Z) (g : X -> Y) (A : Ensemble X)
  : (fun x => f (g x))¹ A = f¹ (g¹ A).
Proof.
  setext. unset. split.
  - intros ? [x [? ->]]. exists (g x). split; auto. now exists x.
  - intros ? [? [[x [? ->]] ->]]. now exists x.
Qed.

Theorem preimage_mono {X Y} (f : X -> Y) (A B : Ensemble Y)
  : A ⊂ B -> f⁻¹ A ⊂ f⁻¹ B.
Proof. setsolve. Qed.

Theorem preimage_empty {X Y} (f : X -> Y)
  : f⁻¹ ∅ = ∅.
Proof. setsolve. Qed.

Theorem preimage_full {X Y} (f : X -> Y)
  : f⁻¹ ∅ = ∅.
Proof. setsolve. Qed.

Theorem preimage_complement {X Y} (f : X -> Y) (A : Ensemble Y)
  : f⁻¹(A ᶜ) = (f⁻¹ A)ᶜ.
Proof. setsolve. Qed.

Theorem preimage_intersection {X Y} (f : X -> Y) (A B : Ensemble Y)
  : f⁻¹ A ∩ f⁻¹ B = f⁻¹(A ∩ B).
Proof. setsolve. Qed.

Theorem preimage_union {X Y} (f : X -> Y) (A B : Ensemble Y)
  : f⁻¹ A ∪ f⁻¹ B = f⁻¹(A ∪ B).
Proof. setsolve. Qed.

Theorem preimage_family_intersection {X Y I} (f : X -> Y) (F : I -> Ensemble Y)
  : f⁻¹(FamilyIntersection F) = ⋂i => f⁻¹(F i).
Proof. setsolve. Qed.

Theorem preimage_family_union {X Y I} (f : X -> Y) (F : I -> Ensemble Y)
  : f⁻¹(FamilyUnion F) = ⋃i => f⁻¹(F i).
Proof. setsolve. Qed.

Theorem preimage_set_intersection {X Y} (f : X -> Y) (F : Ensemble (Ensemble Y))
  : f⁻¹(∩F) = ∩((f⁻¹)¹ F).
Proof.
  setext. unset. split.
  - intros x p ? [A [? ->]]. auto with sets.
  - intros x p A ?.
    rewrite <- preimage_char.
    apply (p (f⁻¹ A)). eauto.
Qed.

Theorem preimage_set_union {X Y} (f : X -> Y) (F : Ensemble (Ensemble Y))
  : f⁻¹(∪F) = ∪((f⁻¹)¹ F).
Proof.
  setext. unset. split.
  - intros x [A []].
    exists (f⁻¹ A). eauto with sets.
  - intros x [? [[A [? ->]]]]. unset.
    now exists A.
Qed.

Theorem image_is_empty {X Y} (f : X -> Y)
  : (X -> False) <-> is_empty (Image f).
Proof. setsolve_firstorder. Qed.

Theorem direct_image_is_empty {X Y} (f : X -> Y) (A : Ensemble X)
  : is_empty A <-> is_empty (f¹ A).
Proof. setsolve_firstorder. Qed.

Theorem preimage_is_empty {X Y} (f : X -> Y) (A : Ensemble Y)
  : is_empty A -> is_empty (f⁻¹ A).
Proof. setsolve. Qed.

Theorem preimage_identity {X} (A : Ensemble X)
  : (fun x => x)⁻¹ A = A.
Proof. setsolve. Qed.

Theorem preimage_composition {X Y Z} (f : Y -> Z) (g : X -> Y) (A : Ensemble Z)
  : (fun x => f (g x))⁻¹ A = g⁻¹ (f⁻¹ A).
Proof. setsolve. Qed.

Theorem image_preimage {X Y} (f : X -> Y) (A : Ensemble Y)
  : f¹(f⁻¹ A) ⊂ A.
Proof.
  unset. now intros ? [x [? ->]].
Qed.

Theorem image_preimage_surj {X Y} (f : X -> Y) (A : Ensemble Y)
  : Surjective f -> f¹(f⁻¹ A) = A.
Proof.
  unfold Surjective. intros s.
  setext. split.
  - apply image_preimage.
  - unset. intros y p.
    destruct (s y) as [x <-].
    now exists x.
Qed.

Theorem image_is_full {X Y} (f : X -> Y)
  : Surjective f <-> is_full (Image f).
Proof.
  split.
  - intros s y.
    destruct (s y) as [x <-].
    now eexists.
  - intros p y.
    destruct (p y).
    now eexists.
Qed.

Theorem direct_image_is_full {X Y} (f : X -> Y) (A : Ensemble X)
  : is_full A -> Surjective f -> is_full (f¹ A).
Proof.
  intros p s y.
  destruct (s y) as [x <-].
  now constructor.
Qed.

Theorem preimage_is_full {X Y} (f : X -> Y) (A : Ensemble Y)
  : is_full A -> is_full (f⁻¹ A).
Proof. setsolve. Qed.

Theorem complement_is_full {X} (A : Ensemble X)
  : is_empty A <-> is_full (A ᶜ).
Proof. setsolve. Qed.

Theorem complement_is_empty {X} (A : Ensemble X)
  : is_full A <-> is_empty (A ᶜ).
Proof.
  split.
  - setsolve.
  - intros p x. apply NNPP.
    intros ?. now apply (p x).
Qed.

Theorem family_intersection_set {X I} (F : I -> Ensemble X)
  : FamilyIntersection F = ∩Image F.
Proof. setsolve_firstorder. Qed.

Theorem family_union_set {X I} (F : I -> Ensemble X)
  : FamilyUnion F = ∪Image F.
Proof. setsolve_firstorder. Qed.
