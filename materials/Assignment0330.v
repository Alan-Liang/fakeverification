Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Require Import PV.HoareLogic.
Local Open Scope string.
Local Open Scope list.
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       HoareSimpleWhile
       HoareSimpleWhile_Derived
       HoareSimpleWhile_Admissible.

(** 习题：*)

(** 如果if语句的两个分支具有不同的后条件，那么整个if语句以什么为后条件呢？可以以
    他们的析取为后条件。先定义析取：*)

Definition orp (P Q: assertion): assertion := fun s => P s \/ Q s.

Notation "x || y" := (orp x y)
  (in custom assn_entry at level 15, left associativity).

Ltac assn_unfold ::=
  unfold derives, andp, orp.

(** 下面证明下面规则是导出规则：*)

Lemma hoare_if_disj:
  forall P e c1 c2 Q1 Q2,
    provable {{ P && [[ e ]] }} c1 {{ Q1 }} ->
    provable {{ P && [[! e ]] }} c2 {{ Q2 }} ->
    provable {{ P }} if (e) then { c1 } else { c2 } {{ Q1 || Q2 }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 当然，上面这条规则也不会破坏可靠性：*)

Lemma hoare_if_disj_sound:
  forall P e c1 c2 Q1 Q2,
    valid {{ P && [[ e ]] }} c1 {{ Q1 }} ->
    valid {{ P && [[! e ]] }} c2 {{ Q2 }} ->
    valid {{ P }} if (e) then { c1 } else { c2 } {{ Q1 || Q2 }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)
Lemma hoare_skip_inv: forall P Q,
  provable {{ P }} skip {{ Q }} -> P |--  Q.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)
Lemma hoare_while_inv: forall P Q e c,
  provable {{ P }} while (e) do { c } {{ Q }} ->
  exists I,
    derives P I /\
    provable {{ I && [[ e ]] }} c {{ I }} /\
    Assn (I && [[! e]]) |-- Q.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)

(** 提示：下面引理的证明中需要用到前面证明过的诸多_[inv]_性质。归纳证明的前两种
    已经完成证明了，请完成剩余的证明。*)

Lemma hoare_disj_pre: forall P1 P2 c Q,
  provable {{ P1 }} c {{ Q }} ->
  provable {{ P2 }} c {{ Q }} ->
  provable {{ P1 || P2 }} c {{ Q }}.
Proof.
  intros.
  revert P1 P2 Q H H0; induction c; intros.
  + apply hoare_skip_inv in H.
    apply hoare_skip_inv in H0.
    apply (hoare_conseq_post _ _ (Assn(P1 || P2))).
    - apply hoare_skip.
    - assn_tauto H H0.
  + apply hoare_asgn_fwd_inv in H.
    apply hoare_asgn_fwd_inv in H0.
    eapply hoare_conseq_post; [apply hoare_asgn_fwd |].
    revert H H0; unfold derives, exp, andp, ei2exprZ, exprZ_eq, orp;
      unfold_substs; intros.
    destruct H1 as [x' [? ?] ].
    destruct H2.
    - apply H.
      exists x'; tauto.
    - apply H0.
      exists x'; tauto.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)

(** 有上面性质可以立即推出下面结论。*)

Lemma hoare_disj: forall P1 P2 c Q1 Q2,
  provable {{ P1 }} c {{ Q1 }} ->
  provable {{ P2 }} c {{ Q2 }} ->
  provable {{ P1 || P2 }} c {{ Q1 || Q2 }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)

(** 下面引理是_[hoare_if_seq]_的逆命题。*)

Lemma hoare_if_seq2: forall P Q e c1 c2 c3,
  provable {{ P }} if (e) then { c1; c3 } else { c2; c3 } {{ Q }} ->
  provable {{ P }} if (e) then { c1 } else { c2 }; c3 {{ Q }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)

(** 下面性质说明，循环与其展开一层后的行为是等价的。*)

Lemma hoare_loop_unroll1: forall P Q e c,
  provable {{ P }} if (e) then { c; while (e) do { c } } else { skip } {{ Q }} <->
  provable {{ P }} while (e) do { c } {{ Q }}.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

