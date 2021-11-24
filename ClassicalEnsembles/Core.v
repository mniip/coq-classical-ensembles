Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Classes.RelationClasses.

Require Export Coq.Sets.Ensembles.

Arguments In {X} A x : rename.
Arguments Included {X} A B : rename.
Module SetElementNotation.
Notation "x ∈ A" := (In A x)
  (at level 69).
Notation "A ⊂ B" := (Included A B)
  (at level 69).
End SetElementNotation.
Import SetElementNotation.

Global Instance subset_reflexive {X} : Reflexive (@Included X).
Proof. now intros A x. Qed.

Global Instance subset_transitive {X} : Transitive (@Included X).
Proof. intros A B C ? ? x. auto. Qed.

Definition is_full {X} (A : Ensemble X) : Prop := forall x, x ∈ A.
Definition is_empty {X} (A : Ensemble X) : Prop := forall x, ~x ∈ A.

Global Hint Extern 2 (_ ∈ _) => unfold In : sets.
Global Hint Extern 1 (is_full _) => unfold is_full : sets.
Global Hint Extern 1 (is_empty _) => unfold is_empty : sets.

Theorem ensemble_extensionality {X} (A B : Ensemble X)
  : (A ⊂ B /\ B ⊂ A) = (A = B).
Proof.
  apply propositional_extensionality. split.
  - intros [p q]. apply functional_extensionality.
    intros ?. apply propositional_extensionality.
    split.
    + apply p.
    + apply q.
  - intros ->. split; now intros ?.
Qed.

Theorem choice_dependent {X Y} (R : forall (x : X), Y x -> Prop)
  : (forall x, exists y, R x y) -> exists f, forall x, R x (f x).
Proof.
  intros h.
  set (R' x v := exists (p : projT1 v = x), R x (eq_rect _ _ (projT2 v) _ p)).
  assert (exists f, forall x, R' x (f x)) as f. {
    apply choice. intros x.
    destruct (h x) as [y].
    exists (existT _ x y).
    unfold R'. now exists eq_refl.
  }
  destruct f as [f e].
  unshelve eexists.
  - intros x. replace x with (projT1 (f x)). 
    + apply projT2. 
    + now destruct (e x).
  - simpl. intros x. now destruct (e x) as [<-].
Qed.

Definition EnsembleLEM {X} (P : Prop) (T : P -> Ensemble X) (F : ~P -> Ensemble X) : Ensemble X
  := fun x => (exists p, x ∈ T p) \/ (exists p, x ∈ F p).

Theorem ensemble_lem_true {X} {P : Prop} (T : P -> Ensemble X) (F : ~P -> Ensemble X) p
  : EnsembleLEM P T F = T p.
Proof.
  rewrite <- ensemble_extensionality. split.
  - intros ? [[q] | []].
    + now rewrite (proof_irrelevance _ p q).
    + contradiction.
  - left. now exists p.
Qed.

Theorem ensemble_lem_false {X} {P : Prop} (T : P -> Ensemble X) (F : ~P -> Ensemble X) p
  : EnsembleLEM P T F = F p.
Proof.
  rewrite <- ensemble_extensionality. split.
  - intros ? [[] | [q]].
    + contradiction.
    + now rewrite (proof_irrelevance _ p q).
  - right. now exists p.
Qed.
