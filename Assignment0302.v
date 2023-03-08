Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import PV.Syntax.
Import Lang_While.
Require Import PV.PracticalDenotations.
Import DntSem_While.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.
Arguments Rels.concat: simpl never.

(** 习题：*)

(** 请证明以下两条关于_[Rels.test]_的性质。*)

Lemma Rels_test_empty: forall X: state -> Prop,
  X == ∅ ->
  Rels.test X == ∅.
Proof.
  unfold_RELS_tac.
  intros.
  sets_unfold in H.
  split.
  - intro.
    destruct H0.
    rewrite <- (H a).
    apply H0.
  - tauto.
Qed.

Lemma Rels_test_full: forall X: state -> Prop,
  X == Sets.full ->
  Rels.test X == Rels.id.
Proof.
  unfold_RELS_tac.
  intros.
  sets_unfold in H.
  split; intro.
  - destruct H0.
    apply H1.
  - split.
    + apply H.
      tauto.
    + tauto.
Qed.


(** 习题：*)

(** 请证明：如果循环条件恒为真且循环体的行为不改变程序状态，循环是不会终止的。 *)

Lemma inf_loop_nrm: forall e c n,
  test_true (eval_expr e) == Rels.id ->
  test_false (eval_expr e) == ∅ ->
  (eval_com c).(nrm) == Rels.id ->
  iter_nrm_lt_n (eval_expr e) (eval_com c) n == ∅.
Proof.
  intros.
  induction n; try reflexivity.
  simpl.
  rewrite H, H0, H1, IHn.
  rewrite ! Rels_concat_id_l.
  rewrite Sets_union_empty.
  reflexivity.
Qed.

(** 习题：*)

(** 请证明：如果循环条件恒为真且循环体的行为不改变程序状态，循环是不会运行出错的。 *)

Lemma inf_loop_err: forall e c n,
  test_true (eval_expr e) == Rels.id ->
  (eval_expr e).(err) == ∅ ->
  (eval_com c).(nrm) == Rels.id ->
  (eval_com c).(err) == ∅ ->
  iter_err_lt_n (eval_expr e) (eval_com c) n == ∅.
Proof.
  intros.
  revert n.
  induction n; try reflexivity.
  simpl.
  rewrite H, H0, H1, H2, IHn.
  rewrite ! Rels_concat_id_l.
  rewrite ! Sets_union_empty.
  reflexivity.
Qed.
