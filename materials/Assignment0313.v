Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import SetsClass.SetsClass.
Require Import compcert.lib.Integers.
Import SetsNotation.
Require Import PV.Syntax.
Import Lang_While.
Require Import PV.PracticalDenotations.
Import DntSem_While.
Require Import PV.EquivAndRefine.
Require Import PV.Assignment0306.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.
Arguments Rels.id: simpl never.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

(** 习题：*)

(** 先前，我们证明过_[remove_skip]_操作过后的程序语句中不会再在顺序执行的任何一
    侧出现_[skip]_。下面请证明_[remove_skip]_操作能保持语义等价。*)

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

Lemma remove_skip_sound: forall c,
  remove_skip c ~=~ c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 下面定义的_[right_assoc]_操作能将所有的顺序执行语法树变为右结合的形式。而
    _[CSeq_right_assoc]_是其中要用到的辅助定义。*)

Fixpoint CSeq_right_assoc (c c0: com): com :=
  match c with
  | CSeq c1 c2 => CSeq c1 (CSeq_right_assoc c2 c0)
  | _ => CSeq c c0
  end.

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

(** 下面请分两步证明：_[right_assoc]_变换前后的程序是语义等价的。*)

Lemma CSeq_right_assoc_sound: forall c c0,
    CSeq_right_assoc c c0 ~=~ [[c ; c0]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma right_assoc_sound: forall c,
  right_assoc c ~=~ c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

Module StatewiseEequiv.

(** 下面我们将定义一种新的更细粒度的等价关系_[statewise_eequiv]_，可以用符号：
    _[e1 @ s1 ~=~ e2 @ e2]_表示。其含义是，_[e1]_在_[s1]_这个程序状态上的求值结
    果与_[e2]_在_[s2]_这个程序状态上的求值结果相同。如果

       _[H: e1 @ s1 ~=~ e2 @ e2]_

    那么 _[H.(nrm_eequiv_s): forall i, ⟦ e1 ⟧.(nrm) s1 i <-> ⟦ e2 ⟧.(nrm) s2 i]_
    并且 _[H.(err_eequiv_s): ⟦ e1 ⟧.(err) s1 <-> ⟦ e2 ⟧.(err) s2]_。

    如果反过来，需要证明_[e1 @ s1 ~=~ e2 @ e2]_，那么可以用_[skip; simpl]_来拆解
    这一结论。下面是相关定义，可以忽略其中的细节。*)

Record statewise_eequiv
         (p1: expr * state)
         (p2: expr * state): Prop :=
{
  nrm_eequiv_s':
    forall i, ⟦ fst p1 ⟧.(nrm) (snd p1) i <-> ⟦ fst p2 ⟧.(nrm) (snd p2) i;
  err_eequiv_s':
    ⟦ fst p1 ⟧.(err) (snd p1) <-> ⟦ fst p2 ⟧.(err) (snd p2);
}.

Notation "e @ s" := (@pair expr state e s) (at level 59, no associativity).
Notation "p1 '~=~' p2" := (statewise_eequiv p1 p2)
  (at level 69, only printing, no associativity).
Ltac any_equiv x y ::=
  match type of x with
  | expr => exact (eequiv x y)
  | com => exact (cequiv x y)
  | prod expr state => exact (statewise_eequiv x y)
  | _ => match type of y with
         | expr => exact (eequiv x y)
         | com => exact (cequiv x y)
         | prod expr state => exact (statewise_eequiv x y)
         end
  end.

Lemma nrm_eequiv_s: forall (e1 e2: expr) (s1 s2: state),
  (e1 @ s1) ~=~ (e2 @ s2) ->
  forall i, ⟦ e1 ⟧.(nrm) s1 i <-> ⟦ e2 ⟧.(nrm) s2 i.
Proof. intros ? ? ? ?. apply nrm_eequiv_s'. Qed.

Lemma err_eequiv_s: forall (e1 e2: expr) (s1 s2: state),
  (e1 @ s1) ~=~ (e2 @ s2) ->
  (⟦ e1 ⟧.(err) s1 <-> ⟦ e2 ⟧.(err) s2).
Proof. intros ? ? ? ?. apply err_eequiv_s'. Qed.

Notation "x '.(nrm_eequiv_s)'" := (nrm_eequiv_s _ _ _ _ x)
  (at level 1).

Notation "x '.(err_eequiv_s)'" := (err_eequiv_s _ _ _ _ x)
  (at level 1).

(** 下面请证明，这种细粒度的等价关系也是一种等价关系。*)

Instance statewise_eequiv_refl:
  Reflexive statewise_eequiv.
Proof.
  unfold Reflexive.
  intros [e s].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance statewise_eequiv_sym:
  Symmetric statewise_eequiv.
Proof.
  unfold Symmetric.
  intros [e1 s1] [e2 s2].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance statewise_eequiv_trans:
  Transitive statewise_eequiv.
Proof.
  unfold Transitive.
  intros [e1 s1] [e2 s2] [e3 s3].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 下面我们的引理证明了二元运算符与一元运算符能够保持这种_[statewise_eequiv]_关
    系。这些证明不需要你完成。*)

Lemma arith_sem1_nrm_congr_s:
  forall Zfun (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    forall i,
      arith_sem1_nrm Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) s1 i <->
      arith_sem1_nrm Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) s2 i.
Proof.
  intros.
  unfold arith_sem1_nrm.
  apply ex_iff_morphism; intros i1.
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  apply and_iff_morphism; [apply H0.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma arith_sem1_err_congr_s:
  forall Zfun (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    ((⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ∪
      arith_sem1_err Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm)) s1) <->
    ((⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
      arith_sem1_err Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm)) s2).
Proof.
  intros.
  unfold arith_sem1_err.
  apply or_iff_morphism.
  + apply or_iff_morphism.
    - apply H.(err_eequiv_s).
    - apply H0.(err_eequiv_s).
  + apply ex_iff_morphism; intros i1.
    apply ex_iff_morphism; intros i2.
    apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
    apply and_iff_morphism; [apply H0.(nrm_eequiv_s) |].
    reflexivity.
Qed.

Lemma arith_sem2_nrm_congr_s:
  forall int64fun (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    forall i,
      arith_sem2_nrm int64fun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) s1 i <->
      arith_sem2_nrm int64fun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) s2 i.
Proof.
  intros.
  unfold arith_sem2_nrm.
  apply ex_iff_morphism; intros i1.
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  apply and_iff_morphism; [apply H0.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma arith_sem2_err_congr_s:
  forall (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    (⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err) ∪
      arith_sem2_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm)) s1 <->
    (⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err) ∪
      arith_sem2_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm)) s2.
Proof.
  intros.
  unfold arith_sem2_err.
  apply or_iff_morphism.
  + apply or_iff_morphism.
    - apply H.(err_eequiv_s).
    - apply H0.(err_eequiv_s).
  + apply ex_iff_morphism; intros i1.
    apply ex_iff_morphism; intros i2.
    apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
    apply and_iff_morphism; [apply H0.(nrm_eequiv_s) |].
    reflexivity.
Qed.

Lemma cmp_sem_nrm_congr_s:
  forall op (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    forall i,
      cmp_sem_nrm op ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) s1 i <->
      cmp_sem_nrm op ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) s2 i.
Proof.
  intros.
  unfold cmp_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  apply and_iff_morphism; [apply H0.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma cmp_sem_err_congr_s:
  forall (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    (⟦ e11 ⟧.(err) ∪ ⟦ e21 ⟧.(err)) s1 <->
    (⟦ e12 ⟧.(err) ∪ ⟦ e22 ⟧.(err)) s2.
Proof.
  intros.
  apply or_iff_morphism.
  + apply H.(err_eequiv_s).
  + apply H0.(err_eequiv_s).
Qed.

Lemma and_sem_nrm_congr_s:
  forall (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    forall i,
      and_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) s1 i <->
      and_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) s2 i.
Proof.
  intros.
  unfold and_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  apply or_iff_morphism; [reflexivity |].
  apply and_iff_morphism; [reflexivity |].
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H0.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma and_sem_err_congr_s:
  forall (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    (⟦ e11 ⟧.(err) ∪ and_sem_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(err)) s1 <->
    (⟦ e12 ⟧.(err) ∪ and_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err)) s2.
Proof.
  intros.
  unfold and_sem_err.
  apply or_iff_morphism; [apply H.(err_eequiv_s) |].
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  apply and_iff_morphism; [| apply H0.(err_eequiv_s)].
  reflexivity.
Qed.

Lemma or_sem_nrm_congr_s:
  forall (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    forall i,
      or_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) s1 i <->
      or_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) s2 i.
Proof.
  intros.
  unfold or_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  apply or_iff_morphism; [reflexivity |].
  apply and_iff_morphism; [reflexivity |].
  apply ex_iff_morphism; intros i2.
  apply and_iff_morphism; [apply H0.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma or_sem_err_congr_s:
  forall (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    (⟦ e11 ⟧.(err) ∪ or_sem_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(err)) s1 <->
    (⟦ e12 ⟧.(err) ∪ or_sem_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(err)) s2.
Proof.
  intros.
  unfold or_sem_err.
  apply or_iff_morphism; [apply H.(err_eequiv_s) |].
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  apply and_iff_morphism; [| apply H0.(err_eequiv_s)].
  reflexivity.
Qed.

Lemma not_sem_nrm_congr_s:
  forall (e1 e2: expr) (s1 s2: state),
    e1 @ s1 ~=~ e2 @ s2 ->
    forall i,
      not_sem_nrm ⟦ e1 ⟧.(nrm) s1 i <->
      not_sem_nrm ⟦ e2 ⟧.(nrm) s2 i.
Proof.
  intros.
  unfold not_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma not_sem_err_congr_s:
  forall (e1 e2: expr) (s1 s2: state),
    e1 @ s1 ~=~ e2 @ s2 ->
    ⟦ e1 ⟧.(err) s1 <-> ⟦ e2 ⟧.(err) s2.
Proof.
  intros.
  apply H.(err_eequiv_s).
Qed.

Lemma neg_sem_nrm_congr_s:
  forall (e1 e2: expr) (s1 s2: state),
    e1 @ s1 ~=~ e2 @ s2 ->
    forall i,
      neg_sem_nrm ⟦ e1 ⟧.(nrm) s1 i <->
      neg_sem_nrm ⟦ e2 ⟧.(nrm) s2 i.
Proof.
  intros.
  unfold neg_sem_nrm.
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma neg_sem_err_congr_s:
  forall (e1 e2: expr) (s1 s2: state),
    e1 @ s1 ~=~ e2 @ s2 ->
    (⟦ e1 ⟧.(err) ∪ neg_sem_err ⟦ e1 ⟧.(nrm)) s1 <->
    (⟦ e2 ⟧.(err) ∪ neg_sem_err ⟦ e2 ⟧.(nrm)) s2.
Proof.
  intros.
  unfold neg_sem_err.
  apply or_iff_morphism; [apply H.(err_eequiv_s) |].
  apply ex_iff_morphism; intros i1.
  apply and_iff_morphism; [apply H.(nrm_eequiv_s) |].
  reflexivity.
Qed.

Lemma EBinop_congr_s:
  forall op (e11 e12 e21 e22: expr) (s1 s2: state),
    e11 @ s1 ~=~ e12 @ s2 ->
    e21 @ s1 ~=~ e22 @ s2 ->
    EBinop op e11 e21 @ s1 ~=~ EBinop op e12 e22 @ s2.
Proof.
  intros.
  destruct op.
  + split; simpl.
    - apply or_sem_nrm_congr_s; tauto.
    - apply or_sem_err_congr_s; tauto.
  + split; simpl.
    - apply and_sem_nrm_congr_s; tauto.
    - apply and_sem_err_congr_s; tauto.
  + split; simpl.
    - apply cmp_sem_nrm_congr_s; tauto.
    - apply cmp_sem_err_congr_s; tauto.
  + split; simpl.
    - apply cmp_sem_nrm_congr_s; tauto.
    - apply cmp_sem_err_congr_s; tauto.
  + split; simpl.
    - apply cmp_sem_nrm_congr_s; tauto.
    - apply cmp_sem_err_congr_s; tauto.
  + split; simpl.
    - apply cmp_sem_nrm_congr_s; tauto.
    - apply cmp_sem_err_congr_s; tauto.
  + split; simpl.
    - apply cmp_sem_nrm_congr_s; tauto.
    - apply cmp_sem_err_congr_s; tauto.
  + split; simpl.
    - apply cmp_sem_nrm_congr_s; tauto.
    - apply cmp_sem_err_congr_s; tauto.
  + split; simpl.
    - apply arith_sem1_nrm_congr_s; tauto.
    - apply arith_sem1_err_congr_s; tauto.
  + split; simpl.
    - apply arith_sem1_nrm_congr_s; tauto.
    - apply arith_sem1_err_congr_s; tauto.
  + split; simpl.
    - apply arith_sem1_nrm_congr_s; tauto.
    - apply arith_sem1_err_congr_s; tauto.
  + split; simpl.
    - apply arith_sem2_nrm_congr_s; tauto.
    - apply arith_sem2_err_congr_s; tauto.
  + split; simpl.
    - apply arith_sem2_nrm_congr_s; tauto.
    - apply arith_sem2_err_congr_s; tauto.
Qed.

Lemma EUnop_congr_s:
  forall op (e1 e2: expr) (s1 s2: state),
    e1 @ s1 ~=~ e2 @ s2 ->
    EUnop op e1 @ s1 ~=~ EUnop op e2 @ s2.
Proof.
  intros.
  destruct op.
  + split; simpl.
    - apply not_sem_nrm_congr_s; tauto.
    - apply not_sem_err_congr_s; tauto.
  + split; simpl.
    - apply neg_sem_nrm_congr_s; tauto.
    - apply neg_sem_err_congr_s; tauto.
Qed.

(** 下面请你证明两条关于_[statewise_eequiv]_的性质，在证明中可能需要你手动运用上
    面给出的_[EBinop_congr_s]_进行证明。

    下面定义的_[subst_const]_关系说的是：可以将_[e1]_中出现的变量_[x]_替换成常数
    _[n]_得到_[e2]_。如果_[x]_在_[e1]_中出现多次，那么_[subst_const]_关系允许只
    替换其中的0次、1次或任意多次乃至全部。请你分两步证明，如果在程序状态_[s]_上
    变量_[x]_的值是_[n]_，那么上述_[e1]_与_[e2]_满足：_[e1 @ s ~=~ e2 @ s]_。*)

Fixpoint subst_const (e1 e2: expr) (x: var_name) (n: Z): Prop :=
  match e1, e2 with
  | EConst n1, EConst n2 => n1 = n2
  | EVar x1, EVar x2 => x1 = x2
  | EVar x1, EConst n2 => x1 = x /\ n2 = n
  | EBinop op1 e11 e12, EBinop op2 e21 e22 =>
      op1 = op2 /\ subst_const e11 e21 x n /\ subst_const e12 e22 x n
  | EUnop op1 e11, EUnop op2 e21 =>
      op1 = op2 /\ subst_const e11 e21 x n
  | _, _ => False
  end.

(** 这是一条辅助引理：*)

Lemma subst_const_base_sound: forall (s: state) (x: var_name) (n: Z),
  Int64.min_signed <= n <= Int64.max_signed ->
  s x = Vint (Int64.repr n) ->
  x @ s ~=~ n @ s.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 这是最终需要证明的性质：*)

Theorem subst_const_sound: forall (s: state) e1 e2 (x: var_name) n,
  Int64.min_signed <= n <= Int64.max_signed ->
  s x = Vint (Int64.repr n) ->
  subst_const e1 e2 x n ->
  e1 @ s ~=~ e2 @ s.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 下面定义的命题_[appears_in_expr e x]_说的是：程序变量_[x]_会在表达式_[e]_中
    出现至少一次。*)

Fixpoint appears_in_expr (e: expr) (x: var_name): Prop :=
  match e with
  | EConst _ => False
  | EVar y => x = y
  | EBinop op e1 e2 => appears_in_expr e1 x \/ appears_in_expr e2 x
  | EUnop op e1 => appears_in_expr e1 x
  end.

(** 请证明：如果_[e]_中出现的每个变量都在_[s1]_与_[s2]_这两个程序状态上取值相同，
    那么_[e]_在这两个程序状态上的求值结果就相同。*)

Theorem eeval_appears: forall s1 s2 e,
  (forall x: var_name, appears_in_expr e x -> s1 x = s2 x) ->
  e @ s1 ~=~ e @ s2.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

End StatewiseEequiv.

