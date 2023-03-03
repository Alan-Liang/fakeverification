Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import PV.Syntax.
Import Lang_SimpleWhile.
Require Import PV.DenotationalSemantics.
Import DntSem_SimpleWhile2 DntSem_SimpleWhile3 DntSem_SimpleWhile4.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.

(** 习题：*)
(** 下面的递归函数_[remove_skip]_定义了在程序语句中删除多余空语句的操作。*)

Fixpoint remove_skip (c: com): com :=
  match c with
  | CSeq c1 c2 =>
      match remove_skip c1, remove_skip c2 with
      | CSkip, _ => remove_skip c2
      | _, CSkip => remove_skip c1
      | _, _ => CSeq (remove_skip c1) (remove_skip c2)
      end
  | CIf e c1 c2 =>
      CIf e (remove_skip c1) (remove_skip c2)
  | CWhile e c1 =>
      CWhile e (remove_skip c1)
  | _ =>
      c
  end.

(** 下面请证明：_[remove_skip]_之后，确实不再有多余的空语句了。所谓没有空语句，
    是指不出现_[c; SKIP]_或_[SKIP; c]_这样的语句。首先定义：局部不存在多余的空语
    句。*)

Definition not_sequencing_skip (c: com): Prop :=
  match c with
  | CSeq CSkip _ => False
  | CSeq _ CSkip => False
  | _ => True
  end.

(** 其次定义语法树的所有子树中都不存在多余的空语句。*)

Fixpoint no_sequenced_skip (c: com): Prop :=
  match c with
  | CSeq c1 c2 =>
      not_sequencing_skip c /\
      no_sequenced_skip c1 /\ no_sequenced_skip c2
  | CIf e c1 c2 =>
      no_sequenced_skip c1 /\ no_sequenced_skip c2
  | CWhile e c1 =>
      no_sequenced_skip c1
  | _ =>
      True
  end.

(** 下面是需要证明的结论。*)

Theorem remove_skip_no_sequenced_skip: forall c,
  no_sequenced_skip (remove_skip c).
Proof.
  intro.
  induction c; simpl; try tauto.
  - destruct (remove_skip c1), (remove_skip c2);
    simpl;
    tauto.
Qed.


(** 习题：*)
(** 下面我们定义一项简单的程序变换：右结合变换。例如，将_[(c1;c2);c3]_变换为
    _[c1;(c2;c3)]_。*)

(** 首先，这里定义一个辅助函数，该函数假设_[c]_与_[c0]_已经是右结合的，计算
    _[c; c0]_转换后的结果*)

Fixpoint CSeq_right_assoc (c c0: com): com :=
  match c with
  | CSeq c1 c2 => CSeq c1 (CSeq_right_assoc c2 c0)
  | _ => CSeq c c0
  end.

(** 现在，可以在_[CSeq_right_assoc]_的基础上定义右结合变换_[right_assoc]_。*)

Fixpoint right_assoc (c: com): com :=
  match c with
  | CSeq c1 c2 =>
      CSeq_right_assoc (right_assoc c1) (right_assoc c2)
  | CIf e c1 c2 =>
      CIf e (right_assoc c1) (right_assoc c2)
  | CWhile e c1 =>
      CWhile e (right_assoc c1)
  | _ =>
      c
  end.

(** 下面证明：经过右结合变换后，确实程序语句中不再有左结合的结构了。下面分为两步
    定义『无左结合结构』，即_[no_left_assoc]_。*)

Definition not_left_assoc (c: com): Prop :=
  match c with
  | CSeq (CSeq _ _) _ => False
  | _ => True
  end.

Fixpoint no_left_assoc (c: com): Prop :=
  match c with
  | CSeq c1 c2 =>
      not_left_assoc c /\
      no_left_assoc c1 /\ no_left_assoc c2
  | CIf e c1 c2 =>
      no_left_assoc c1 /\ no_left_assoc c2
  | CWhile e c1 =>
      no_left_assoc c1
  | _ =>
      True
  end.

(** 证明也需要分两步进行。请先证明关于_[CSeq_right_assoc]_的引理。*)

Lemma CSeq_right_assoc_no_left_assoc: forall c c0,
  no_left_assoc c ->
  no_left_assoc c0 ->
  no_left_assoc (CSeq_right_assoc c c0).
Proof.
  intros.
  induction c; try (simpl; tauto).
  - destruct H, H1.
    simpl.
    tauto.
Qed.

(** 下面是需要证明的最终结论。*)

Theorem right_assoc_no_left_assoc: forall c,
  no_left_assoc (right_assoc c).
Proof.
  intro.
  induction c; simpl; try tauto.
  - apply CSeq_right_assoc_no_left_assoc; tauto.
Qed.

(** 习题：*)
Example skip_seq_skip:
  eval_com (CSeq CSkip CSkip) == eval_com CSkip.
Proof.
  simpl.
  unfold seq_sem, skip_sem.
  unfold_RELS_tac.
  intros.
  split; intro.
  - destruct H, H.
    rewrite H, H0.
    reflexivity.
  - exists a.
    tauto.
Qed.

(** 习题：*)
Example inc_x_fact: forall s1 s2 n,
  eval_com (CAsgn "x" [["x" + 1]]) s1 s2 ->
  s1 "x" = n ->
  s2 "x" = n + 1.
Proof.
  intros.
  unfold eval_com in H.
  unfold asgn_sem in H.
  destruct H.
  rewrite H.
  clear H.
  simpl.
  unfold add_sem, var_sem, const_sem.
  rewrite H0.
  reflexivity.
Qed.
