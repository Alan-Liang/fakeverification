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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Rels_test_full: forall X: state -> Prop,
  X == Sets.full ->
  Rels.test X == Rels.id.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 请证明：如果循环条件恒为真且循环体的行为不改变程序状态，循环是不会终止的。 *)

Lemma inf_loop_nrm: forall e c n,
  test_true (eval_expr e) == Rels.id ->
  test_false (eval_expr e) == ∅ ->
  (eval_com c).(nrm) == Rels.id ->
  iter_nrm_lt_n (eval_expr e) (eval_com c) n == ∅.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 请证明：如果循环条件恒为真且循环体的行为不改变程序状态，循环是不会运行出错的。 *)

Lemma inf_loop_err: forall e c n,
  test_true (eval_expr e) == Rels.id ->
  (eval_expr e).(err) == ∅ ->
  (eval_com c).(nrm) == Rels.id ->
  (eval_com c).(err) == ∅ ->
  iter_err_lt_n (eval_expr e) (eval_com c) n == ∅.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


