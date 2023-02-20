Require Import PV.Syntax.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.

(** 习题：*)
Lemma size_nonneg: forall t,
  0 <= tree_size t.
Proof.
  intro.
  induction t; simpl.
  - reflexivity.
  - lia.
Qed.

Lemma tree_reverse_inj_lem (t1 t2: tree) (H: tree_reverse t1 = tree_reverse t2):
  t1 = t2.
Proof.
  rewrite <- (reverse_involutive t1).
  rewrite <- (reverse_involutive t2).
  rewrite H.
  reflexivity.
Qed.

(** 习题：*)
Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
Proof.
  intros.
  rewrite <- reverse_involutive in H.
  rewrite (tree_reverse_inj_lem _ _ H).
  simpl.
  reflexivity.
Qed.


(** 习题：*)
(** 下面的_[left_most]_函数与_[right_most]_函数计算了二叉树中最左侧的节点信息与
    最右侧的节点信息。如果树为空，则返回_[default]_。*)

Fixpoint left_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => left_most l n
  end.

Fixpoint right_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => right_most r n
  end.

(** 很显然，这两个函数应当满足：任意一棵二叉树的最右侧节点，就是将其左右翻转之后
    最左侧节点。这个性质可以在Coq中如下描述：*)

Lemma left_most_reverse: forall t default,
  left_most (tree_reverse t) default = right_most t default.
Proof.
  intro.
  induction t; simpl.
  - reflexivity.
  - intro.
    rewrite (IHt2 v).
    reflexivity.
Qed.
