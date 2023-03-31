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
Local Open Scope Z.
Local Open Scope sets.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

Module Task1.
Import Lang_SimpleWhile
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile4
       HoareSimpleWhile.

(** 习题：*)
Lemma hoare_seq_valid_inv: forall P R c1 c2,
  valid {{ P }} c1 ; c2 {{ R }} ->
  exists Q: assertion,
    valid {{ P }} c1 {{ Q }} /\
    valid {{ Q }} c2 {{ R }}.
Proof.
  simpl.
  unfold seq_sem.
  unfold_RELS_tac.
  intros.
  exists (fun s1' : state => exists s1 : state, P s1 /\ eval_com c1 s1 s1').
  split; intros.
  - exists s1.
    exact (conj H0 H1).
  - destruct H0, H0.
    assert (H3 : exists i : state, eval_com c1 x i /\ eval_com c2 i s2). {
      exists s1.
      tauto.
    }
    exact (H _ _ H0 H3).
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


End Task1.

Module Task2.
Import Permutation ListNotations.

(** 习题：*)
Example perm_fact2: Permutation [1; 2; 3] [3; 2; 1].
  apply (perm_trans _ [2;1;3]).
  - apply perm_swap.
  - apply (perm_trans _ [2;3;1]).
    + apply perm_skip, perm_swap.
    + apply perm_swap.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 提示：在证明过程中，既可以考虑对_[list]_元素归纳，也可以用考虑证明树归纳。*)

Lemma Permutation_app_head: forall {A: Type} (l l1 l2 : list A),
  Permutation l1 l2 -> Permutation (l ++ l1) (l ++ l2).
Proof.
  intros.
  induction l; simpl; try tauto.
  apply perm_skip.
  exact IHl.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.RelationClasses.

#[local] Instance Permutation_refl { A : Type } : Reflexive (@Permutation A).
  unfold Reflexive.
  intro.
  apply perm_refl.
Qed.

#[local] Instance Permutation_transitive { A : Type } : Transitive (@Permutation A).
  unfold Transitive.
  intros.
  apply (perm_trans _ _ _ H H0).
Qed.

#[local] Instance Permutation_symmetric { A : Type } : Symmetric (@Permutation A).
  unfold Symmetric.
  intros.
  apply perm_symm.
  exact H.
Qed.

Lemma Permutation_app_tail : forall {A: Type} (l1 l2 l: list A),
  Permutation l1 l2 -> Permutation (l1 ++ l) (l2 ++ l).
Proof.
  intros.
  induction H; simpl.
  - reflexivity.
  - apply perm_skip.
    tauto.
  - apply perm_swap.
  - apply (perm_trans _ _ _ IHPermutation1 IHPermutation2).
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 提示：如果可以选择对多棵证明树作归纳证明，请仔细辨别选择。*)

Lemma Permutation_app: forall {A: Type} (l m l' m': list A),
  Permutation l l' ->
  Permutation m m' ->
  Permutation (l ++ m) (l' ++ m').
Proof.
  intros.
  induction H0; simpl.
  - rewrite ! app_nil_r.
    exact H.
  - eapply perm_trans.
    + apply Permutation_app_head.
      apply perm_skip.
      exact H0.
    + apply Permutation_app_tail.
      exact H.
  - eapply perm_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_app_tail.
      exact H.
  - apply (perm_trans _ _ _ IHPermutation1).
    eapply perm_trans.
    + apply Permutation_app_tail.
      apply (perm_symm _ _ H).
    + tauto.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma app_cons { A : Type } : forall a : A, forall l : list A,
  a :: l = ([a] ++ l)%list.
Proof. reflexivity. Qed.

(** 习题：*)
Lemma Permutation_cons_append: forall {A: Type} (l : list A) x,
  Permutation (x :: l) (l ++ x :: nil).
Proof.
  intros.
  induction l; simpl.
  - reflexivity.
  - eapply perm_trans.
    + apply perm_swap.
    + rewrite app_comm_cons.
      rewrite app_cons.
      rewrite (app_cons a l).
      rewrite <- app_assoc.
      apply Permutation_app_head.
      exact IHl.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Permutation_rev: forall {A: Type} (l: list A),
  Permutation l (rev l).
Proof.
  intros.
  induction l; simpl.
  - reflexivity.
  - eapply perm_trans.
    + apply Permutation_cons_append.
    + apply Permutation_app_tail.
      exact IHl.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 提示：在完成证明的过程中可以灵活使用_[Search]_指令搜索关于_[app]_、_[nil]_等
    定义的性质。*)

Lemma Permutation_app_comm: forall {A : Type} (l l' : list A),
  Permutation (l ++ l') (l' ++ l).
Proof.
  intros.
  induction l; simpl.
  - rewrite app_nil_r.
    reflexivity.
  - apply (perm_trans _ (l ++ l' ++ [a])%list).
    + rewrite app_assoc.
      apply Permutation_cons_append.
    + apply (perm_trans _ (l' ++ l ++ [a])%list).
      * rewrite ! app_assoc.
        apply Permutation_app_tail.
        exact IHl.
      * apply Permutation_app_head.
        apply perm_symm.
        apply Permutation_cons_append.
Qed. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


End Task2.
