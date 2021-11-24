Require Import Coq.Logic.PropExtensionality.

Require Import ClassicalEnsembles.Core.
Require Import ClassicalEnsembles.Tactics.

Import SetElementNotation.

(* Defined in Coq.Sets.Ensembles.
Inductive Intersection (U : Type) (B C : Ensemble U) : Ensemble U
  := Intersection_intro : forall x : U, x ∈ B -> x ∈ C -> x ∈ B ∩ C.
Inductive Union (U : Type) (B C : Ensemble U) : Ensemble U
  := Union_introl : forall x : U, x ∈ B -> x ∈ B ∪ C
  | Union_intror : forall x : U, x ∈ C -> x ∈ B ∪ C.
Inductive Empty_set (U : Type) : Ensemble U := .
Inductive Full_set (U : Type) : Ensemble U
  := Full_intro : forall x : U, x ∈ Full_set U.
Defiition Complement (U : Type) (A : Ensemble U) : Ensemble U := fun x => ~x ∈ A.
*)
Arguments Intersection {X} A B : rename.
Arguments Union {X} A B : rename.
Arguments Empty_set {X} : rename.
Arguments Full_set {X} : rename.
Arguments Complement {X} A : rename.

Module SetAlgebraNotation.

Notation "A ∩ B" := (Intersection A B)
  (at level 67, left associativity).
Notation "A ∪ B" := (Union A B)
  (at level 68, left associativity).
Notation "'∅'" := Empty_set.
Notation "'⊤'" := Full_set.
Notation "A 'ᶜ'" := (Complement A)
  (at level 65).
Notation "A \ B" := (Intersection A (Complement _ B))
  (at level 67, left associativity, only parsing).

End SetAlgebraNotation.
Import SetAlgebraNotation.

Theorem empty_is_empty {X}
  : @is_empty X ∅.
Proof. intros ? []. Qed.

Theorem is_empty_empty {X} (A : Ensemble X)
  : is_empty A = (A = ∅).
Proof.
  apply propositional_extensionality. split.
  - intros p. rewrite <- ensemble_extensionality. split.
    + intros x ?. contradiction (p x).
    + intros ? [].
  - intros ->. apply empty_is_empty.
Qed.

Theorem full_is_full {X}
  : @is_full X ⊤.
Proof. constructor. Qed.

Theorem is_full_full {X} (A : Ensemble X)
  : is_full A = (A = ⊤).
Proof.
  apply propositional_extensionality. split.
  - intros p. rewrite <- ensemble_extensionality. split.
    + constructor.
    + intros x ?. apply (p x).
  - intros ->. apply full_is_full.
Qed.

Theorem intersection_char {X} (A B : Ensemble X) x 
  : x ∈ A ∩ B = (x ∈ A /\ x ∈ B).
Proof.
  apply propositional_extensionality. split.
  - intros p. now destruct p.
  - intros []. auto with sets.
Qed.

Theorem union_char {X} (A B : Ensemble X) x
  : x ∈ A ∪ B = (x ∈ A \/ x ∈ B).
Proof.
  apply propositional_extensionality. split.
  - intros p. destruct p; auto.
  - intros []; now constructor.
Qed.

Theorem empty_char {X} (x : X)
  : x ∈ ∅ = False.
Proof.
  apply propositional_extensionality. split.
  - intros [].
  - intros [].
Qed.

Theorem full_char {X} (x : X)
  : x ∈ ⊤ = True.
Proof.
  apply propositional_extensionality. split.
  - auto.
  - constructor.
Qed.

Theorem complement_char {X} (A : Ensemble X) x
  : x ∈ A ᶜ = ~ x ∈ A.
Proof.
  reflexivity.
Qed.

Global Hint Resolve empty_is_empty : sets.
Global Hint Rewrite @is_empty_empty : sets.
Global Hint Resolve full_is_full : sets.
Global Hint Rewrite @is_full_full : sets.
Global Hint Resolve Full_intro : sets.
Global Hint Rewrite @intersection_char : sets.
Global Hint Rewrite @union_char : sets.
Global Hint Rewrite @empty_char : sets.
Global Hint Rewrite @full_char : sets.
Global Hint Rewrite @complement_char : sets.

Theorem intersection_idem {X} (A : Ensemble X)
  : A ∩ A = A.
Proof. setsolve. Qed.

Theorem intersection_comm {X} (A B : Ensemble X)
  : A ∩ B = B ∩ A.
Proof. setsolve. Qed.

Theorem intersection_assoc {X} (A B C : Ensemble X)
  : A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof. setsolve. Qed.

Theorem intersection_subset_left {X} (A B : Ensemble X)
  : A ∩ B ⊂ A.
Proof. setsolve. Qed.

Theorem intersection_equals_left {X} (A B : Ensemble X)
  : A ⊂ B -> A ∩ B = A.
Proof. setsolve. Qed.

Theorem intersection_subset_right {X} (A B : Ensemble X)
  : A ∩ B ⊂ B.
Proof. setsolve. Qed.

Theorem intersection_equals_right {X} (A B : Ensemble X)
  : B ⊂ A -> A ∩ B = B.
Proof. setsolve. Qed.

Theorem intersection_universal {X} (A B C : Ensemble X)
  : C ⊂ A -> C ⊂ B -> C ⊂ A ∩ B.
Proof. setsolve. Qed.

Theorem union_idem {X} (A : Ensemble X)
  : A ∪ A = A.
Proof. setsolve. Qed.

Theorem union_comm {X} (A B : Ensemble X)
  : A ∪ B = B ∪ A.
Proof. setsolve. Qed.

Theorem union_assoc {X} (A B C : Ensemble X)
  : A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof. setsolve. Qed.

Theorem union_subset_left {X} (A B : Ensemble X)
  : A ⊂ A ∪ B.
Proof. setsolve. Qed.

Theorem union_equals_left {X} (A B : Ensemble X)
  : B ⊂ A -> A ∪ B = A.
Proof. setsolve. Qed.

Theorem union_subset_right {X} (A B : Ensemble X)
  : B ⊂ A ∪ B.
Proof. setsolve. Qed.

Theorem union_equals_right {X} (A B : Ensemble X)
  : A ⊂ B -> A ∪ B = B.
Proof. setsolve. Qed.

Theorem union_universal {X} (A B C : Ensemble X)
  : A ⊂ C -> B ⊂ C -> A ∪ B ⊂ C.
Proof. setsolve. Qed.

Theorem intersection_empty_left {X} (A : Ensemble X)
  : ∅ ∩ A = ∅.
Proof. setsolve. Qed.

Theorem intersection_empty_right {X} (A : Ensemble X)
  : A ∩ ∅ = ∅.
Proof. setsolve. Qed.

Theorem union_empty_left {X} (A : Ensemble X)
  : ∅ ∪ A = A.
Proof. setsolve. Qed.

Theorem union_empty_right {X} (A : Ensemble X)
  : A ∪ ∅ = A.
Proof. setsolve. Qed.

Theorem intersection_full_left {X} (A : Ensemble X)
  : ⊤ ∩ A = A.
Proof. setsolve. Qed.

Theorem intersection_full_right {X} (A : Ensemble X)
  : A ∩ ⊤ = A.
Proof. setsolve. Qed.

Theorem union_full_left {X} (A : Ensemble X)
  : ⊤ ∪ A = ⊤.
Proof. setsolve. Qed.

Theorem union_full_right {X} (A : Ensemble X)
  : A ∪ ⊤ = ⊤.
Proof. setsolve. Qed.

Theorem empty_universal {X} (A : Ensemble X)
  : ∅ ⊂ A.
Proof. setsolve. Qed.

Theorem empty_equals {X} (A : Ensemble X)
  : A ⊂ ∅ -> A = ∅.
Proof. setsolve. Qed.

Theorem full_universal {X} (A : Ensemble X)
  : A ⊂ ⊤.
Proof. setsolve. Qed.

Theorem full_equals {X} (A : Ensemble X)
  : ⊤ ⊂ A -> A = ⊤.
Proof. setsolve. Qed. 

Theorem union_intersection_distr_right {X} (A B C : Ensemble X)
  : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Proof. setsolve. Qed.

Theorem union_intersection_distr_left {X} (A B C : Ensemble X)
  : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C).
Proof. setsolve. Qed.

Theorem intersection_union_distr_right {X} (A B C : Ensemble X)
  : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof. setsolve. Qed.

Theorem intersection_union_distr_left {X} (A B C : Ensemble X)
  : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C).
Proof. setsolve. Qed.

Theorem complement_complement {X} (A : Ensemble X)
  : A ᶜ ᶜ = A.
Proof. setsolve. Qed.

Theorem complement_intersection {X} (A B : Ensemble X)
  : (A ∩ B)ᶜ = A ᶜ ∪ B ᶜ.
Proof. setsolve. Qed.

Theorem complement_union {X} (A B : Ensemble X)
  : (A ∪ B)ᶜ = A ᶜ ∩ B ᶜ.
Proof. setsolve. Qed.

Theorem complement_empty {X}
  : ∅ ᶜ = ⊤ :> Ensemble X.
Proof. setsolve. Qed.

Theorem complement_full {X}
  : ⊤ ᶜ = ∅ :> Ensemble X.
Proof. setsolve. Qed.

Theorem intersection_complement_left {X} (A : Ensemble X)
  : A ᶜ ∩ A = ∅.
Proof. setsolve. Qed.

Theorem intersection_complement_right {X} (A : Ensemble X)
  : A ∩ A ᶜ = ∅.
Proof. setsolve. Qed.

Theorem union_complement_left {X} (A : Ensemble X)
  : A ᶜ ∪ A = ⊤.
Proof. setsolve. Qed.

Theorem union_complement_right {X} (A : Ensemble X)
  : A ∪ A ᶜ = ⊤.
Proof. setsolve. Qed.

Theorem complement_subset {X} (A B : Ensemble X)
  : A ⊂ B = B ᶜ ⊂ A ᶜ.
Proof.
  apply propositional_extensionality. setsolve.
Qed.

Theorem subset_cartesian_adjunction {X} (A B C : Ensemble X)
  : A ∩ B ⊂ C = A ⊂ B ᶜ ∪ C.
Proof.
  apply propositional_extensionality. setsolve. firstorder.
Qed.

Theorem subset_cocartesian_adjunction {X} (A B C : Ensemble X)
  : A ⊂ B ∪ C = A ∩ B ᶜ ⊂ C.
Proof.
  apply propositional_extensionality. setsolve. firstorder.
Qed.

Theorem intersection_is_empty_left {X} (A B : Ensemble X)
  : is_empty A -> is_empty (A ∩ B).
Proof. setsolve. Qed.

Theorem intersection_is_empty_right {X} (A B : Ensemble X)
  : is_empty B -> is_empty (A ∩ B).
Proof. setsolve. Qed.

Theorem union_is_empty {X} (A B : Ensemble X)
  : is_empty A /\ is_empty B <-> is_empty (A ∪ B).
Proof. setsolve. Qed.

Theorem intersection_is_full {X} (A B : Ensemble X)
  : is_full A /\ is_full B <-> is_full (A ∩ B).
Proof. setsolve_firstorder. Qed.

Theorem union_is_full_left {X} (A B : Ensemble X)
  : is_full A -> is_full (A ∪ B).
Proof. setsolve. Qed.

Theorem union_is_full_right {X} (A B : Ensemble X)
  : is_full B -> is_full (A ∪ B).
Proof. setsolve. Qed.
