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
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


End Task1.

Module Task2.
Import Permutation ListNotations.

(** 习题：*)
Example perm_fact2: Permutation [1; 2; 3] [3; 2; 1].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 提示：在证明过程中，既可以考虑对_[list]_元素归纳，也可以用考虑证明树归纳。*)

Lemma Permutation_app_head: forall {A: Type} (l l1 l2 : list A),
  Permutation l1 l2 -> Permutation (l ++ l1) (l ++ l2).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Permutation_app_tail : forall {A: Type} (l1 l2 l: list A),
  Permutation l1 l2 -> Permutation (l1 ++ l) (l2 ++ l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 提示：如果可以选择对多棵证明树作归纳证明，请仔细辨别选择。*)

Lemma Permutation_app: forall {A: Type} (l m l' m': list A),
  Permutation l l' ->
  Permutation m m' ->
  Permutation (l ++ m) (l' ++ m').
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)
Lemma Permutation_cons_append: forall {A: Type} (l : list A) x,
  Permutation (x :: l) (l ++ x :: nil).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Permutation_rev: forall {A: Type} (l: list A),
  Permutation l (rev l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)

(** 提示：在完成证明的过程中可以灵活使用_[Search]_指令搜索关于_[app]_、_[nil]_等
    定义的性质。*)

Lemma Permutation_app_comm: forall {A : Type} (l l' : list A),
  Permutation (l ++ l') (l' ++ l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


End Task2.
