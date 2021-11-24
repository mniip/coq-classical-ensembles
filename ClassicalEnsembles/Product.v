Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.ClassicalChoice.

Require Import ClassicalEnsembles.Core.
Require Import ClassicalEnsembles.Tactics.
Require Import ClassicalEnsembles.Algebra.
Require Import ClassicalEnsembles.Families.
Require Import ClassicalEnsembles.Maps.

Import SetElementNotation.
Import SetAlgebraNotation.
Import SetFamilyNotation.
Import SetImageNotation.

Inductive Cartesian {X Y} (A : Ensemble X) (B : Ensemble Y) : Ensemble (X * Y)
  := Cartesian_intro : forall x y, x ∈ A -> y ∈ B -> (x, y) ∈ Cartesian A B.
Inductive Unit : Ensemble unit
  := Unit_intro : tt ∈ Unit.
Inductive FamilyCartesian {I E} (F : forall (i : I), Ensemble (E i)) : Ensemble (forall i, E i)
  := FamilyCartesian_intro : forall f, (forall i, f i ∈ F i) -> f ∈ FamilyCartesian F.

Module SetCartesianNotation.

Notation "A × B" := (Cartesian A B)
  (at level 66, left associativity).
Notation "∏ p => e" := (FamilyCartesian (fun p => e))
  (at level 66, left associativity).
Notation "∏ ' p => e" := (FamilyCartesian (fun p => e))
  (at level 66, left associativity, p strict pattern).

End SetCartesianNotation.
Import SetCartesianNotation.

Global Hint Resolve Cartesian_intro : sets.
Global Hint Resolve Unit_intro : sets.
Global Hint Resolve FamilyCartesian_intro : sets.

Theorem cartesian_char {X Y} (A : Ensemble X) (B : Ensemble Y) x y
  : (x, y) ∈ A × B = (x ∈ A /\ y ∈ B).
Proof.
  apply propositional_extensionality. split.
  - now inversion 1.
  - now intros [].
Qed.

Theorem cartesian_char_eta {X Y} (A : Ensemble X) (B : Ensemble Y) p
  : p ∈ A × B = (fst p ∈ A /\ snd p ∈ B).
Proof.
  apply propositional_extensionality. split.
  - now intros [].
  - now destruct p.
Qed.

Theorem unit_char x
  : x ∈ Unit = True.
Proof.
  apply propositional_extensionality. split; auto.
  now destruct x.
Qed.

Theorem family_cartesian_char {I E} (F : forall (i : I), Ensemble (E i)) f
  : f ∈ FamilyCartesian F = forall i, f i ∈ F i.
Proof.
  apply propositional_extensionality. split; auto with sets.
  now intros [].
Qed.

Global Hint Rewrite @cartesian_char : sets.
Global Hint Rewrite @cartesian_char_eta : sets.
Global Hint Rewrite @unit_char : sets.
Global Hint Rewrite @family_cartesian_char : sets.

Theorem cartesian_mono {X Y} (A1 A2 : Ensemble X) (B1 B2 : Ensemble Y)
  : A1 ⊂ A2 -> B1 ⊂ B2 -> A1 × B1 ⊂ A2 × B2.
Proof. setsolve. Qed.

Theorem family_cartesian_mono {I E} (F1 F2 : forall (i : I), Ensemble (E i))
  : (forall i, F1 i ⊂ F2 i) -> FamilyCartesian F1 ⊂ FamilyCartesian F2.
Proof. setsolve. Qed.

Theorem cartesian_empty_left {X Y} (A : Ensemble Y)
  : ∅ × A = ∅ :> Ensemble (X * Y).
Proof. setsolve. Qed.

Theorem cartesian_empty_right {X Y} (A : Ensemble X)
  : A × ∅ = ∅ :> Ensemble (X * Y).
Proof. setsolve. Qed.

Theorem family_cartesian_empty {I E} (F : forall (i : I), Ensemble (E i)) i
  : F i = ∅ -> FamilyCartesian F = ∅.
Proof. setsolve. Qed.

Theorem cartesian_full {X Y}
  : ⊤ × ⊤ = ⊤ :> Ensemble (X * Y).
Proof. setsolve. Qed.

Theorem family_cartesian_full {I E} (F : forall (i : I), Ensemble (E i))
  : (forall i, F i = ⊤) -> FamilyCartesian F = ⊤.
Proof.
  intros p. apply full_equals. unset.
  intros f _ i. now rewrite p.
Qed.

Theorem cartesian_is_empty {X Y} (A : Ensemble X) (B : Ensemble Y)
  : is_empty A \/ is_empty B <-> is_empty (A × B).
Proof.
  split.
  - intros [i | j] ? [x y].
    + now apply (i x).
    + now apply (j y).
  - intros u. apply NNPP. intros [i j]%not_or_and.
    apply i. intros x ?. apply j. intros y ?.
    specialize (u (x, y)).
    now apply u.
Qed.

Theorem family_cartesian_is_empty {I E} (F : forall (i : I), Ensemble (E i))
  : (exists i, is_empty (F i)) <-> is_empty (FamilyCartesian F).
Proof.
  split.
  - setsolve_firstorder.
  - unfold is_empty. unset.
    intros u. apply NNPP. intros ne.
    assert (exists f, forall i, f i ∈ F i) as [f].
    {
      apply choice_dependent. intros i. apply NNPP.
      intros n. apply ne. exists i. intros x ?.
      apply n. now exists x.
    }
    now apply (u f).
Qed.

Theorem cartesian_is_full {X Y} (A : Ensemble X) (B : Ensemble Y)
  : (X -> False) \/ (Y -> False) \/ (is_full A /\ is_full B) <-> is_full (A × B).
Proof.
  split.
  - intros [ | [ | [p q]]].
    + intros []. contradiction.
    + intros []. contradiction.
    + intros []. specialize (p x). now specialize (q y).
  - intros p.
    destruct (classic (inhabited X)) as [[x] | ].
    + destruct (classic (inhabited Y)) as [[y] | ].
      * right. right. split.
        ** intros x'. specialize (p (x', y)). setsolve.
        ** intros y'. specialize (p (x, y')). setsolve.
      * right. left. auto.
    + left. auto.
Qed.

Theorem family_cartesian_is_full {I E} (F : forall (i : I), Ensemble (E i))
  : (exists i, E i -> False) \/ (forall i, is_full (F i)) <-> is_full (FamilyCartesian F).
Proof.
  split.
  - intros [[i] | p].
    + intros f. contradiction (f i).
    + intros f. constructor. intros i. apply p.
  - intros p.
    destruct (classic (exists i, E i -> False)) as [ | ne]; auto.
    right.
    assert (exists (f : forall i, E i), forall (i : I), True) as [f].
    {
      apply (choice_dependent (fun _ _ => True)).
      intros i. apply NNPP. intros n.
      apply ne. exists i. intros ?. now apply n.
    }
    intros i x.
    apply classic_set_in_prop_context. intros lem.
    set (f' j := match lem (i = j) with
                     | left e => eq_rect _ E x _ e
                     | right _ => f j
                     end).
    replace x with (f' i).
    + now destruct (p f').
    + subst f'. simpl.
      destruct lem as [e | ].
      * replace e with (@eq_refl _ i); auto.
        apply proof_irrelevance.
      * contradiction.
Qed.

Theorem intersection_cartesian {X Y} (A1 A2 : Ensemble X) (B1 B2 : Ensemble Y)
  : (A1 × B1) ∩ (A2 × B2) = (A1 ∩ A2) × (B1 ∩ B2).
Proof. setsolve. Qed.

Theorem intersection_family_cartesian {I E} (F G : forall (i : I), Ensemble (E i))
  : FamilyCartesian F ∩ FamilyCartesian G = ∏ i => (F i ∩ G i).
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_cartesian {I X Y} (F : I -> Ensemble X) (G : I -> Ensemble Y)
  : ⋂ i => F i × G i = FamilyIntersection F × FamilyIntersection G.
Proof. setsolve_firstorder. Qed.

Theorem family_intersection_family_cartesian {I J E} (F : J -> forall (i : I), Ensemble (E i))
  : ⋂ j => FamilyCartesian (F j) = ∏ i => ⋂ j => F j i.
Proof. setsolve. Qed.

Theorem complement_cartesian {X Y} (A : Ensemble X) (B : Ensemble Y)
  : (A × B)ᶜ = (A ᶜ × B) ∪ (A × B ᶜ) ∪ (A ᶜ × B ᶜ).
Proof. setsolve. Qed.

Theorem fst_image_empty {X Y}
  : (Y -> False) -> Image (@fst X Y) = ∅.
Proof.
  intros ?. apply empty_equals. unset.
  now intros ? [[x y] ->].
Qed.

Theorem fst_image_full {X Y}
  : Y -> Image (@fst X Y) = ⊤.
Proof.
  intros y. apply full_equals. unset.
  intros x. now exists (x, y).
Qed.

Theorem snd_image_empty {X Y}
  : (X -> False) -> Image (@snd X Y) = ∅.
Proof.
  intros ?. apply empty_equals. unset.
  now intros ? [[x y] ->].
Qed.

Theorem snd_image_full {X Y}
  : X -> Image (@snd X Y) = ⊤.
Proof.
  intros x. apply full_equals. unset.
  intros y. now exists (x, y).
Qed.

Theorem projection_image_empty {I} (E : I -> Type) i
  : (E i -> False) -> Image (fun (f : forall i, E i) => f i) = ∅.
Proof.
  intros ?. apply empty_equals. unset.
  intros x [f ->]. auto.
Qed.

Theorem projection_image_full {I} (E : I -> Type) i
  : (forall i, E i) -> Image (fun (f : forall i, E i) => f i) = ⊤.
Proof.
  intros f. apply full_equals. unset.
  intros x _.
  apply classic_set_in_prop_context. intros lem.
  exists (fun j => match lem (i = j) with
                   | left e => eq_rect _ E x _ e
                   | right _ => f j
                   end).
  destruct lem as [e | ].
  - replace e with (@eq_refl _ i); auto.
    apply proof_irrelevance.
  - contradiction.
Qed.

Theorem fst_direct_image_cartesian {X Y} (A : Ensemble X) (B : Ensemble Y) y
  : y ∈ B -> fst¹ (A × B) = A.
Proof.
  intros ?. setext. unset. split.
  - now intros ? [[x' y'] [[] ->]].
  - intros x. now exists (x, y).
Qed.

Theorem snd_direct_image_cartesian {X Y} (A : Ensemble X) (B : Ensemble Y) x
  : x ∈ A -> snd¹ (A × B) = B.
Proof.
  intros ?. setext. unset. split.
  - now intros ? [[x' y'] [[] ->]].
  - intros y. now exists (x, y).
Qed.

Theorem projection_direct_image_cartesian {I E} (F : forall (i : I), Ensemble (E i)) i
  : (forall i, exists x, x ∈ F i) -> (fun f => f i)¹ (FamilyCartesian F) = F i.
Proof.
  intros ?. setext. unset. split.
  - now intros x [f [? ->]].
  - intros x ?.
    assert (exists f, forall i, f i ∈ F i) as [f].
    {
      now apply choice_dependent.
    }
    apply classic_set_in_prop_context. intros lem.
    exists (fun j => match lem (i = j) with
                     | left e => eq_rect _ E x _ e
                     | right _ => f j
                     end).
    split.
    + intros j. destruct lem as [-> | ]; auto.
    + destruct lem as [e | ].
      * replace e with (@eq_refl _ i); auto.
        apply proof_irrelevance.
      * contradiction.
Qed.

Theorem fst_preimage {X Y} (A : Ensemble X)
  : fst⁻¹ A = A × ⊤ :> Ensemble (X * Y).
Proof. setsolve. Qed.

Theorem snd_preimage {X Y} (A : Ensemble Y)
  : snd⁻¹ A = ⊤ × A :> Ensemble (X * Y).
Proof. setsolve. Qed.

Theorem projection_preimage {I E} (F : forall (i : I), Ensemble (E i)) i (A : Ensemble (E i))
  : (fun (f : forall i, E i) => f i)⁻¹ A = ∏ j => EnsembleLEM (i = j) (eq_rect _ (fun i => Ensemble (E i)) A _) (fun _ => ⊤).
Proof.
  setext. unset. split.
  - intros f ? j.
    destruct (classic (i = j)) as [p | p].
    + rewrite (ensemble_lem_true _ _ p).
      now destruct p.
    + now rewrite (ensemble_lem_false _ _ p).
  - intros f u. specialize (u i).
    now rewrite (ensemble_lem_true _ _ eq_refl) in u.
Qed.
