Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FinFun.

Require Import ClassicalEnsembles.Core.
Require Import ClassicalEnsembles.Tactics.
Require Import ClassicalEnsembles.Algebra.

Import SetElementNotation.
Import SetAlgebraNotation.

Inductive FamilyIntersection {X I} (F : I -> Ensemble X) : Ensemble X
  := FamilyIntersection_intro : forall x, (forall i, x ∈ F i) -> x ∈ FamilyIntersection F.
Inductive FamilyUnion {X I} (F : I -> Ensemble X) : Ensemble X
  := FamilyUnion_intro : forall x i, x ∈ F i -> x ∈ FamilyUnion F.
Inductive SetIntersection {X} (F : Ensemble (Ensemble X)) : Ensemble X
  := SetIntersection_intro : forall x, (forall A, A ∈ F -> x ∈ A) -> x ∈ SetIntersection F.
Inductive SetUnion {X} (F : Ensemble (Ensemble X)) : Ensemble X
  := SetUnion_intro : forall x A, A ∈ F -> x ∈ A -> x ∈ SetUnion F.

Module SetFamilyNotation.

Notation "⋂ p => e" := (FamilyIntersection (fun p => e))
  (at level 67, left associativity).
Notation "⋂ ' p => e" := (FamilyIntersection (fun p => e))
  (at level 67, left associativity, p strict pattern).
Notation "⋃ p => e" := (FamilyUnion (fun p => e))
  (at level 68, left associativity).
Notation "⋃ ' p => e" := (FamilyUnion (fun p => e))
  (at level 68, left associativity, p strict pattern).
Notation "∩ F" := (SetIntersection F)
  (at level 67, left associativity).
Notation "∪ F" := (SetUnion F)
  (at level 68, left associativity).

End SetFamilyNotation.
Import SetFamilyNotation.

Theorem family_intersection_char {X I} {F : I -> Ensemble X} x
  : x ∈ FamilyIntersection F = forall i, x ∈ F i.
Proof.
  apply propositional_extensionality. split.
  - intros p. now destruct p.
  - now constructor.
Qed.

Theorem family_union_char {X I} {F : I -> Ensemble X} x
  : x ∈ FamilyUnion F = exists i, x ∈ F i.
Proof.
  apply propositional_extensionality. split.
  - intros p. destruct p as [? i]. now exists i.
  - intros [i]. now exists i.
Qed.

Theorem set_intersection_char {X} {F : Ensemble (Ensemble X)} x
  : x ∈ ∩F = forall A, A ∈ F -> x ∈ A.
Proof.
  apply propositional_extensionality. split.
  - intros p. now destruct p.
  - now constructor.
Qed.

Theorem set_union_char {X} {F : Ensemble (Ensemble X)} x
  : x ∈ ∪F = exists A, A ∈ F /\ x ∈ A.
Proof.
  apply propositional_extensionality. split.
  - intros p. destruct p as [? A]. now exists A.
  - intros [A []]. now exists A.
Qed.

Global Hint Resolve FamilyIntersection_intro FamilyUnion_intro : sets.
Global Hint Resolve SetIntersection_intro SetUnion_intro : sets.
Global Hint Rewrite @family_intersection_char : sets.
Global Hint Rewrite @family_union_char : sets.
Global Hint Rewrite @set_intersection_char : sets.
Global Hint Rewrite @set_union_char : sets.

Theorem intersection_any_empty {X I} (F : I -> Ensemble X) i
  : F i = ∅ -> ⋂ i => F i = ∅.
Proof. setsolve. Qed.

Theorem union_any_full {X I} (F : I -> Ensemble X) i
  : F i = ⊤ -> ⋃ i => F i = ⊤.
Proof. setsolve. Qed.

Theorem family_union_complement {X I} (F : I -> Ensemble X)
  : ⋂ i => (F i ᶜ) = (⋃ i => F i)ᶜ.
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_complement {X I} (F : I -> Ensemble X)
  : ⋃ i => (F i ᶜ) = (⋂ i => F i)ᶜ.
Proof.
  setext. unset. split.
  - intros x [i] ?. auto.
  - intros x p. apply NNPP. intros q.
    apply p. intros i. apply NNPP. intros ?.
    apply q. now exists i.
Qed.

Theorem family_intersection_subset {X I} (F : I -> Ensemble X) i
  : (⋂ i => F i) ⊂ F i.
Proof. setsolve. Qed.

Theorem family_intersection_equal_element {X I} (F : I -> Ensemble X) i
  : (forall j, F i ⊂ F j) -> (⋂ i => F i) = F i.
Proof. setsolve. Qed.

Theorem family_intersection_universal {X I} (F : I -> Ensemble X) A
  : (forall i, A ⊂ F i) -> A ⊂ (⋂ i => F i).
Proof. setsolve. Qed.

Theorem family_union_subset {X I} (F : I -> Ensemble X) i
  : F i ⊂ (⋃ i => F i).
Proof. setsolve. Qed.

Theorem family_union_equal_element {X I} (F : I -> Ensemble X) i
  : (forall j, F j ⊂ F i) -> (⋃ i => F i) = F i.
Proof. setsolve_firstorder. Qed.

Theorem family_union_universal {X I} (F : I -> Ensemble X) A
  : (forall i, F i ⊂ A) -> (⋃ i => F i) ⊂ A.
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_union_right {X I} (F : I -> Ensemble X) A
  : (⋂ i => F i) ∪ A = ⋂ i => (F i ∪ A).
Proof.
  setsolve. apply NNPP. firstorder.
Qed.

Theorem family_intersection_union_left {X I} (F : I -> Ensemble X) A
  : A ∪ (⋂ i => F i) = ⋂ i => (A ∪ F i).
Proof.
  setsolve. apply NNPP. firstorder.
Qed.

Theorem family_union_intersection_right {X I} (F : I -> Ensemble X) A
  : (⋃ i => F i) ∩ A = ⋃ i => (F i ∩ A).
Proof. setsolve_firstorder. Qed.

Theorem family_union_intersection_left {X I} (F : I -> Ensemble X) A
  : A ∩ (⋃ i => F i) = ⋃ i => (A ∩ F i).
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_distr {X I J} (F : I -> Ensemble X) (G : J -> Ensemble X)
  : (⋂ i => F i) ∪ (⋂ j => G j) = ⋂ ij => (F (fst ij) ∪ G (snd ij)).
Proof.
  setext. unset. split.
  - intros x []. all: intros [i j]; auto.
  - intros x p.
    destruct (classic (exists i, ~x ∈ F i)) as [[i] | n].
    + right. intros j. now destruct (p (pair i j)).
    + left. intros i. apply NNPP. intros ?.
      apply n. now exists i.
Qed.

Theorem family_union_distr {X I J} (F : I -> Ensemble X) (G : J -> Ensemble X)
  : (⋃ i => F i) ∩ (⋃ j => G j) = ⋃ ij => (F (fst ij) ∩ G (snd ij)).
Proof.
  setext. unset. split.
  - intros x [[i] [j]]. now exists (pair i j).
  - intros x [[i j] []]. eauto.
Qed.

Theorem family_intersection_reindex {X I J} (F : I -> Ensemble X) (m : J -> I)
  : ⋂ i => F i ⊂ ⋂ j => F (m j).
Proof. setsolve. Qed.

Theorem family_intersection_reindex_surj {X I J} (F : I -> Ensemble X) (m : J -> I)
  : Surjective m -> ⋂ j => F (m j) = ⋂ i => F i.
Proof.
  unfold Surjective. intros s.
  setext. unset. split.
  - intros x p i. now destruct (s i) as [j <-].
  - auto.
Qed.

Theorem family_union_reindex {X I J} (F : I -> Ensemble X) (m : J -> I)
  : ⋃ j => F (m j) ⊂ ⋃ i => F i.
Proof. setsolve_firstorder. Qed.

Theorem family_union_reindex_surj {X I J} (F : I -> Ensemble X) (m : J -> I)
  : Surjective m -> ⋃ j => F (m j) = ⋃ i => F i.
Proof.
  unfold Surjective. intros s.
  setext. unset. split.
  - firstorder.
  - intros x [i]. destruct (s i) as [j <-]. eauto.
Qed.

Theorem family_intersection_zip {X I} (F G : I -> Ensemble X)
  : (⋂ i => F i) ∩ (⋂ i => G i) = ⋂ i => (F i ∩ G i).
Proof. setsolve_firstorder. Qed.

Theorem family_union_zip {X I} (F G : I -> Ensemble X)
  : (⋃ i => F i) ∪ (⋃ i => G i) = ⋃ i => (F i ∪ G i).
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_binary {X} (A B : Ensemble X)
  : A ∩ B = ⋂ b => if b : bool then A else B.
Proof.
  setext. unset. split.
  - now intros x [] [].
  - intros x p. split.
    + apply (p true).
    + apply (p false).
Qed.

Theorem family_union_binary {X} (A B : Ensemble X)
  : A ∪ B = ⋃ b => if b : bool then A else B.
Proof.
  setext. unset. split.
  - intros x [].
    + now exists true.
    + now exists false.
  - intros x [[]]; auto.
Qed.

Theorem family_intersection_unary {X} (A : Ensemble X)
  : FamilyIntersection (fun u : unit => A) = A.
Proof. setsolve. Qed.

Theorem family_union_unary {X} (A : Ensemble X)
  : FamilyUnion (fun u : unit => A) = A.
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_empty {X}
  : ⊤ = ⋂ f => match f : False with end :> Ensemble X.
Proof. setsolve. Qed.

Theorem family_union_empty {X}
  : ∅ = ⋃ f => match f : False with end :> Ensemble X.
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_sum {X I J} (F : I + J -> Ensemble X)
  : ⋂ ij => F ij = (⋂ i => F (inl i)) ∩ (⋂ j => F (inr j)).
Proof. setsolve. Qed.

Theorem family_intersection_sum_eta {X I J} (F : I -> Ensemble X) (G : J -> Ensemble X)
  : (⋂ i => F i) ∩ (⋂ j => G j) = ⋂ ij => match ij with
                                          | inl i => F i
                                          | inr j => G j
                                          end.
Proof.
  rewrite family_intersection_sum. reflexivity.
Qed.

Theorem family_union_sum {X I J} (F : I + J -> Ensemble X)
  : ⋃ ij => F ij = (⋃ i => F (inl i)) ∪ (⋃ j => F (inr j)).
Proof.
  setext. unset. split.
  - intros x [[i | j]].
    + left. now exists i.
    + right. now exists j.
  - intros x [[i] | [j]]; eauto.
Qed.

Theorem family_union_sum_eta {X I J} (F : I -> Ensemble X) (G : J -> Ensemble X)
  : (⋃ i => F i) ∪ (⋃ j => G j) = ⋃ ij => match ij with
                                          | inl i => F i
                                          | inr j => G j
                                          end.
Proof.
  rewrite family_union_sum. reflexivity.
Qed.

Theorem family_intersection_option {X I} (F : option I -> Ensemble X)
  : ⋂ mi => F mi = (⋂ i => F (Some i)) ∩ F None.
Proof.
  setext. unset. split.
  - auto.
  - now intros x [] [].
Qed.

Theorem family_intersection_option_eta {X I} (F : I -> Ensemble X) A
  : (⋂ i => F i) ∩ A = (⋂ mi => match mi with
                                | Some i => F i
                                | None => A
                                end).
Proof.
  rewrite family_intersection_option. reflexivity.
Qed.

Theorem family_union_option {X I} (F : option I -> Ensemble X)
  : ⋃ mi => F mi = (⋃ i => F (Some i)) ∪ F None.
Proof.
  setext. unset. split.
  - intros x [[]]; eauto.
  - intros x [[] | ]; eauto.
Qed.

Theorem family_union_option_eta {X I} (F : I -> Ensemble X) A
  : (⋃ i => F i) ∪ A = (⋃ mi => match mi with
                                | Some i => F i
                                | None => A
                                end).
Proof.
  rewrite family_union_option. reflexivity.
Qed.

Theorem family_intersection_product {X I J} (F : I * J -> Ensemble X)
  : (⋂ ij => F ij) = (⋂ i => ⋂ j => F (pair i j)).
Proof.
  setext. unset. split.
  - auto.
  - now intros x ? [].
Qed.

Theorem family_intersection_product_eta {X I J} (F : I -> J -> Ensemble X)
  : (⋂ i => ⋂ j => F i j) = (⋂ ij => F (fst ij) (snd ij)).
Proof.
  rewrite family_intersection_product. reflexivity.
Qed.

Theorem family_union_product {X I J} (F : I * J -> Ensemble X)
  : (⋃ ij => F ij) = (⋃ i => ⋃ j => F (pair i j)).
Proof.
  setext. unset. split.
  - intros x [[i j]]. exists i. now exists j.
  - intros x [i [j]]. eauto.
Qed.

Theorem family_union_product_eta {X I J} (F : I -> J -> Ensemble X)
  : (⋃ i => ⋃ j => F i j) = (⋃ ij => F (fst ij) (snd ij)).
Proof.
  rewrite family_union_product. reflexivity.
Qed.

Theorem set_intersection_any_empty {X} (F : Ensemble (Ensemble X))
  : ∅ ∈ F -> ∩F = ∅.
Proof. setsolve_firstorder. Qed.

Theorem set_union_any_full {X} (F : Ensemble (Ensemble X))
  : ⊤ ∈ F -> ∪F = ⊤.
Proof. setsolve. Qed.

Theorem set_intersection_complement {X} (F : Ensemble (Ensemble X))
  : ∪(fun A => A ᶜ ∈ F) = (∩F)ᶜ.
Proof.
  setext. unset. split.
  - intros x [A []] p. now apply (p (A ᶜ)).
  - intros x p. apply NNPP. intros u.
    apply p. intros A ?. apply NNPP. intros ?.
    apply u. exists (A ᶜ). unfold In at 1.
    now rewrite complement_complement.
Qed.

Theorem set_union_complement {X} (F : Ensemble (Ensemble X))
  : ∩(fun A => A ᶜ ∈ F) = (∪F)ᶜ.
Proof.
  setext. unset. split.
  - intros x p [A []]. apply (p (A ᶜ)); auto.
    unfold In at 1. now rewrite complement_complement.
  - intros x p A u. apply NNPP. intros v.
    apply p. now exists (A ᶜ).
Qed.

Theorem set_intersection_mono {X} (F G : Ensemble (Ensemble X))
  : F ⊂ G -> ∩G ⊂ ∩F.
Proof. setsolve. Qed.

Theorem set_union_mono {X} (F G : Ensemble (Ensemble X))
  : F ⊂ G -> ∪F ⊂ ∪G.
Proof. setsolve_firstorder. Qed.

Theorem set_intersection_family {X} (F : Ensemble (Ensemble X))
  : ∩F = ⋂A => @proj1_sig _ F A.
Proof.
  setext. unset. split.
  - intros x p [A]. auto.
  - intros x p A u. apply (p (exist _ A u)).
Qed.

Theorem set_union_family {X} (F : Ensemble (Ensemble X))
  : ∪F = ⋃A => @proj1_sig _ F A.
Proof.
  setext. unset. split.
  - intros x [A [p]]. now exists (exist _ A p).
  - intros x [[A]]. now exists A.
Qed.

Theorem set_intersection_subset {X} (F : Ensemble (Ensemble X)) A
  : A ∈ F -> ∩F ⊂ A.
Proof. setsolve. Qed.

Theorem set_intersection_equals_element {X} (F : Ensemble (Ensemble X)) A
  : A ∈ F -> (forall B, B ∈ F -> A ⊂ B) -> ∩F = A.
Proof. setsolve. Qed.

Theorem set_intersection_universal {X} (F : Ensemble (Ensemble X)) A
  : (forall B, B ∈ F -> A ⊂ B) -> A ⊂ ∩F.
Proof. setsolve. Qed.

Theorem set_union_subset {X} (F : Ensemble (Ensemble X)) A
  : A ∈ F -> A ⊂ ∪F.
Proof. setsolve. Qed.

Theorem set_union_equals_element {X} (F : Ensemble (Ensemble X)) A
  : A ∈ F -> (forall B, B ∈ F -> B ⊂ A) -> ∪F = A.
Proof. setsolve_firstorder. Qed.

Theorem set_union_universal {X} (F : Ensemble (Ensemble X)) A
  : (forall B, B ∈ F -> B ⊂ A) -> ∪F ⊂ A.
Proof. setsolve_firstorder. Qed.

Theorem set_intersection_empty {X}
  : ∩∅ = ⊤ :> Ensemble X.
Proof. setsolve. Qed.

Theorem set_intersection_intersection {X} (F G : Ensemble (Ensemble X))
  : (∩F) ∪ (∩G) ⊂ ∩(F ∩ G).
Proof. setsolve. Qed.

Theorem set_intersection_union {X} (F G : Ensemble (Ensemble X))
  : ∩(F ∪ G) = (∩F) ∩ (∩G).
Proof. setsolve. Qed.

Theorem set_union_empty {X}
  : ∪∅ = ∅ :> Ensemble X.
Proof. setsolve_firstorder. Qed.

Theorem set_union_intersection {X} (F G : Ensemble (Ensemble X))
  : ∪(F ∩ G) ⊂ (∪F) ∩ (∪G).
Proof. setsolve_firstorder. Qed.

Theorem set_union_union {X} (F G : Ensemble (Ensemble X))
  : ∪(F ∪ G) = (∪F) ∪ (∪G).
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_is_empty {X I} (F : I -> Ensemble X)
  : (exists i, is_empty (F i)) -> is_empty (⋂i => F i).
Proof. setsolve_firstorder. Qed.

Theorem family_union_is_empty {X I} (F : I -> Ensemble X)
  : (forall i, is_empty (F i)) <-> is_empty (⋃i => F i).
Proof.
  split.
  - now apply family_union_universal.
  - setsolve.
Qed.

Theorem set_intersection_is_empty {X} (F : Ensemble (Ensemble X))
  : (exists A, A ∈ F /\ is_empty A) -> is_empty (∩F).
Proof. setsolve_firstorder. Qed.

Theorem set_union_is_empty {X} (F : Ensemble (Ensemble X))
  : (forall A, A ∈ F -> is_empty A) <-> is_empty (∪F).
Proof.
  split.
  - now apply set_union_universal.
  - setsolve.
Qed.

Theorem family_intersection_is_full {X I} (F : I -> Ensemble X)
  : (forall i, is_full (F i)) <-> is_full (⋂i => F i).
Proof.
  split.
  - intros p x.
    rewrite family_intersection_char.
    intros i. apply p.
  - setsolve.
Qed.

Theorem family_union_is_full {X I} (F : I -> Ensemble X)
  : (exists i, is_empty (F i)) -> is_empty (⋂i => F i).
Proof. setsolve_firstorder. Qed.

Theorem set_intersection_is_full {X} (F : Ensemble (Ensemble X))
  : (forall A, A ∈ F -> is_full A) <-> is_full (∩F).
Proof.
  split.
  - intros p x.
    rewrite set_intersection_char.
    intros A ?. now apply p.
  - setsolve.
Qed.

Theorem set_union_is_full {X} (F : Ensemble (Ensemble X))
  : (exists A, A ∈ F /\ is_full A) -> is_full (∪F).
Proof. setsolve_firstorder. Qed.
