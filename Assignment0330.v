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

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.RelationClasses.

#[local] Instance derives_refl : Reflexive derives.
  unfold Reflexive, derives.
  intros.
  exact H.
Qed.

#[local] Instance derives_trans : Transitive derives.
  unfold Transitive, derives.
  intros.
  exact (H0 _ (H _ H1)).
Qed.

Lemma orp_left : forall P Q, P |-- (orp P Q).
  unfold derives, orp.
  intros.
  left.
  exact H.
Qed.

Lemma orp_right : forall P Q, Q |-- (orp P Q).
  unfold derives, orp.
  intros.
  right.
  exact H.
Qed.

Lemma hoare_if_disj:
  forall P e c1 c2 Q1 Q2,
    provable {{ P && [[ e ]] }} c1 {{ Q1 }} ->
    provable {{ P && [[! e ]] }} c2 {{ Q2 }} ->
    provable {{ P }} if (e) then { c1 } else { c2 } {{ Q1 || Q2 }}.
Proof.
  intros.
  pose proof (derives_refl (Assn (P && [[e]]))).
  pose proof (orp_left Q1 Q2).
  pose proof (hoare_conseq _ _ _ _ _ H H1 H2).
  clear H H1 H2.
  pose proof (derives_refl (Assn (P && [[! e]]))).
  pose proof (orp_right Q1 Q2).
  pose proof (hoare_conseq _ _ _ _ _ H0 H H1).
  clear H0 H H1.
  apply hoare_if; tauto.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 当然，上面这条规则也不会破坏可靠性：*)

Lemma hoare_if_disj_sound:
  forall P e c1 c2 Q1 Q2,
    valid {{ P && [[ e ]] }} c1 {{ Q1 }} ->
    valid {{ P && [[! e ]] }} c2 {{ Q2 }} ->
    valid {{ P }} if (e) then { c1 } else { c2 } {{ Q1 || Q2 }}.
Proof.
  intros.
  apply hoare_if_sound.
  - eapply hoare_conseq_sound.
    + apply H.
    + reflexivity.
    + apply orp_left.
  - eapply hoare_conseq_sound.
    + apply H0.
    + reflexivity.
    + apply orp_right.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Ltac eq_ind H Heqh :=
  induction H;
  try discriminate;
  intros;
  injection Heqh;
  clear Heqh;
  intros.

(** 习题：*)
Lemma hoare_skip_inv: forall P Q,
  provable {{ P }} skip {{ Q }} -> P |--  Q.
Proof.
  intros.
  remember {{P}} skip {{Q}}.
  revert P Q Heqh.
  eq_ind H Heqh.
  - subst P0 Q.
    reflexivity.
  - subst P0 Q0 c.
    specialize (IHprovable P' Q' eq_refl).
    transitivity P'; try tauto.
    transitivity Q'; tauto.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)
Lemma hoare_while_inv: forall P Q e c,
  provable {{ P }} while (e) do { c } {{ Q }} ->
  exists I,
    derives P I /\
    provable {{ I && [[ e ]] }} c {{ I }} /\
    Assn (I && [[! e]]) |-- Q.
Proof.
  intros.
  remember {{P}} while e do {c} {{Q}}.
  revert P Q Heqh.
  eq_ind H Heqh.
  - subst Q c0 e0 P0.
    clear IHprovable.
    exists P.
    split; [ | split]; try reflexivity.
    tauto.
  - subst Q0 c0 P0.
    specialize (IHprovable P' Q' eq_refl).
    destruct IHprovable as [I' [? [? ?] ] ].
    exists I'.
    split; [ | split]; try tauto.
    + transitivity P'; tauto.
    + transitivity Q'; tauto.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma hoare_while_inv': forall P Q e c,
  (exists I,
    derives P I /\
    provable {{ I && [[ e ]] }} c {{ I }} /\
    Assn (I && [[! e]]) |-- Q) ->
  provable {{ P }} while (e) do { c } {{ Q }}.
Proof.
  intros.
  destruct H as [ R [? [? ? ] ] ].
  apply (hoare_conseq _ R _ Assn( R && [[!e]])); try tauto.
  apply hoare_while; tauto.
Qed.


(** 习题：*)

(** 提示：下面引理的证明中需要用到前面证明过的诸多_[inv]_性质。归纳证明的前两种
    已经完成证明了，请完成剩余的证明。*)

Lemma orp_andp_dist : forall P1 P2 P3,
  Assn ((P1 || P2) && P3) --||-- Assn ((P1 && P3) || (P2 && P3)).
Proof.
  unfold orp, andp, logical_equiv.
  intros.
  tauto.
Qed.

Lemma logical_equiv_derives : forall P Q,
  P --||-- Q -> P |-- Q.
Proof.
  unfold derives.
  intros.
  unfold logical_equiv in H.
  specialize (H s).
  tauto.
Qed.

#[local] Instance logical_equiv_symm : Symmetric logical_equiv.
  unfold Symmetric.
  unfold logical_equiv.
  intros.
  specialize (H s).
  tauto.
Qed.

#[local] Instance logical_equiv_refl : Reflexive logical_equiv.
  unfold Reflexive, logical_equiv.
  intros.
  tauto.
Qed.

Lemma logical_equiv_provable_congr : forall P1 P2 c Q,
  P1 --||-- P2 ->
  provable {{P1}} c {{Q}} <-> provable {{P2}} c {{Q}}.
Proof.
  intros.
  split; intro; eapply hoare_conseq_pre; try apply H0.
  - apply logical_equiv_derives; symmetry; tauto.
  - apply logical_equiv_derives; tauto.
Qed.

Lemma orp_derives_congr : forall P1 P2 Q1 Q2,
  P1 |-- Q1 ->
  P2 |-- Q2 ->
  (orp P1 P2) |-- (orp Q1 Q2).
Proof.
  unfold orp, derives.
  intros.
  specialize (H0 s).
  specialize (H s).
  tauto.
Qed.

Lemma orp_split : forall P1 P2 Q,
  P1 |-- Q ->
  P2 |-- Q ->
  (orp P1 P2) |-- Q.
Proof.
  unfold orp, derives.
  intros.
  specialize (H0 s).
  specialize (H s).
  tauto.
Qed.

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
  + apply hoare_seq_inv in H.
    apply hoare_seq_inv in H0.
    destruct H as [R1 [? ?] ].
    destruct H0 as [R2 [? ?] ].
    apply (hoare_seq _ Assn (R1 || R2)).
    - apply IHc1.
      * apply (hoare_conseq_post P1 _ R1); try tauto.
        apply orp_left.
      * apply (hoare_conseq_post P2 _ R2); try tauto.
        apply orp_right.
    - apply IHc2; tauto.
  + apply hoare_if_inv in H.
    apply hoare_if_inv in H0.
    destruct H, H0.
    apply hoare_if;
    apply (logical_equiv_provable_congr _ _ _ _ (orp_andp_dist _ _ _));
    [apply IHc1 | apply IHc2];
    tauto.
  + apply hoare_while_inv in H.
    apply hoare_while_inv in H0.
    destruct H as [I1 [? [? ?] ] ].
    destruct H0 as [I2 [? [? ?] ] ].
    apply hoare_while_inv'.
    exists Assn (I1 || I2).
    split; [ | split].
    - apply orp_derives_congr; tauto.
    - apply (logical_equiv_provable_congr _ _ _ _ (orp_andp_dist _ _ _));
      apply IHc.
      * eapply hoare_conseq_post.
        ++ apply H1.
        ++ apply orp_left.
      * eapply hoare_conseq_post.
        ++ apply H3.
        ++ apply orp_right.
    - eapply derives_trans.
      * apply logical_equiv_derives.
        apply orp_andp_dist.
      * apply orp_split; tauto.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)

(** 有上面性质可以立即推出下面结论。*)

Lemma hoare_disj: forall P1 P2 c Q1 Q2,
  provable {{ P1 }} c {{ Q1 }} ->
  provable {{ P2 }} c {{ Q2 }} ->
  provable {{ P1 || P2 }} c {{ Q1 || Q2 }}.
Proof.
  intros.
  apply hoare_disj_pre; eapply hoare_conseq_post.
  - apply H.
  - apply orp_left.
  - apply H0.
  - apply orp_right.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)

(** 下面引理是_[hoare_if_seq]_的逆命题。*)

Lemma hoare_if_seq2: forall P Q e c1 c2 c3,
  provable {{ P }} if (e) then { c1; c3 } else { c2; c3 } {{ Q }} ->
  provable {{ P }} if (e) then { c1 } else { c2 }; c3 {{ Q }}.
Proof.
  intros.
  apply hoare_if_inv in H.
  destruct H.
  apply hoare_seq_inv in H, H0.
  destruct H as [R1 [? ?] ], H0 as [R2 [? ?] ].
  eapply hoare_seq.
  - apply hoare_if; eapply hoare_conseq_post.
    + apply H.
    + apply orp_left.
    + apply H0.
    + apply orp_right.
  - apply hoare_disj_pre; tauto.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 习题：*)

(** 下面性质说明，循环与其展开一层后的行为是等价的。*)

Lemma hoare_loop_unroll1: forall P Q e c,
  provable {{ P }} if (e) then { c; while (e) do { c } } else { skip } {{ Q }} <->
  provable {{ P }} while (e) do { c } {{ Q }}.
Proof.
  intros.
  split; intro.
  - apply hoare_if_inv in H; destruct H.
    apply hoare_seq_inv in H; destruct H as [Rs [? ?] ].
    apply hoare_while_inv in H1; destruct H1 as [Rw [? [? ?] ] ].
    apply hoare_skip_inv in H0.
    eapply hoare_conseq.
    + apply hoare_while.
      eapply (logical_equiv_provable_congr _ _ _ _ (orp_andp_dist _ _ _)).
      apply hoare_disj_pre; eapply hoare_conseq_post.
      * apply H.
      * transitivity Rw; try tauto.
        apply orp_right.
      * apply H2.
      * apply orp_right.
    + apply orp_left.
    + eapply derives_trans.
      * apply logical_equiv_derives.
        apply orp_andp_dist.
      * apply orp_split; tauto.
  - apply hoare_while_inv in H; destruct H as [R [? [? ?] ] ].
    apply hoare_if.
    + eapply hoare_seq.
      * eapply hoare_conseq_pre.
        apply H0.
        unfold derives, andp.
        intro.
        specialize (H s).
        tauto.
      * eapply hoare_conseq_post.
        ++ apply hoare_while; tauto.
        ++ tauto.
    + eapply (hoare_conseq _ Assn (R && [[! e]])).
      * apply hoare_skip.
      * unfold derives, andp.
        intro.
        specialize (H s).
        tauto.
      * tauto.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
