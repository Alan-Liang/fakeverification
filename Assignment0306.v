Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Import SetsNotation.
Require Import PV.Syntax.
Import Lang_While.
Require Import PV.PracticalDenotations.
Import DntSem_While.
Require Import PV.EquivAndRefine.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.
Arguments Rels.id: simpl never.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

(** 习题：*)
Theorem Rels_concat_empty_r:
  forall {A B: Type} (x: A -> B -> Prop),
    x ∘ ∅ == ∅.
Proof.
  intros.
  unfold_RELS_tac.
  intros.
  split; try tauto.
  intro.
  destruct H.
  tauto.
Qed.

(** 习题：*)
Theorem CSeq_CSkip: forall c,
  [[ c; skip ]] ~=~ c.
Proof.
  intro.
  split; simpl.
  - apply Rels_concat_id_r.
  - rewrite Rels_concat_empty_r.
    apply Sets_union_empty.
  - rewrite Rels_concat_empty_r.
    apply Sets_union_empty.
Qed.

(** 习题：*)
Theorem CSkip_CSeq: forall c,
  [[ skip; c ]] ~=~ c.
Proof.
  intro.
  split;
  simpl;
  rewrite Rels_concat_id_l;
  try reflexivity;
  apply Sets_empty_union.
Qed.

(* unused *)
Lemma Sets_indexed_union_unfold { T : Type } (sets : nat -> T -> T -> Prop) :
  ⋃ sets == sets 0%nat ∪ ⋃ (fun x : nat => sets (S x)).
Proof.
  sets_unfold.
  split; intro.
  - destruct H, x; [ left | right ].
    + apply H.
    + exists x.
      apply H.
  - destruct H.
    + exists 0%nat.
      apply H.
    + destruct H.
      exists (S x).
      apply H.
Qed.

(** 习题：*)
Theorem CWhile_unroll_nrm: forall (e: expr) (c: com),
  ⟦ if e then { c ; while (e) do {c} } else { skip } ⟧.(nrm) ==
  ⟦ while (e) do {c} ⟧.(nrm).
Proof.
  intros.
  simpl.
  rewrite Rels_concat_id_r.
  sets_unfold.
  split; simpl; intro.
  - destruct H.
    + revert H; unfold_RELS_tac; intro.
      destruct H, H, H0, H0, H1.
      exists (S x1).
      simpl.
      unfold_RELS_tac.
      left.
      exists x; split; try apply H.
      exists x0; split; try apply H0.
      apply H1.
    + exists 1%nat.
      simpl.
      unfold_RELS_tac.
      right.
      apply H.
  - destruct H.
    destruct x; try tauto.
    simpl in H.
    revert H; unfold_RELS_tac; intro.
    destruct H, H.
    + destruct H, H0, H0.
      left.
      exists x0; split; try apply H.
      exists x1; split; try apply H0.
      exists x; apply H1.
    + destruct H0.
      right.
      simpl in H.
      unfold test_false.
      unfold_RELS_tac.
      tauto.
Qed.
