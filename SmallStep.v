Require Import PV.Syntax.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import compcert.lib.Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Module SmallStep.
Import Lang_SimpleWhile.

Definition state: Type := var_name -> Z.

Inductive istep (s : state) : expr_int -> expr_int -> Prop :=
| IS_Var : forall x,
    istep s (EVar x) (EConst (s x))
| IS_Add_0 : forall v1 v2,
    istep s (EAdd (EConst v1) (EConst v2)) (EConst (v1 + v2))
| IS_Add_1 : forall e1 e1' e2,
    istep s e1 e1' ->
    istep s (EAdd e1 e2) (EAdd e1' e2)
| IS_Add_2 : forall v1 e2 e2',
    istep s e2 e2' ->
    istep s (EAdd (EConst v1) e2) (EAdd (EConst v1) e2')
| IS_Sub_0 : forall v1 v2,
    istep s (ESub (EConst v1) (EConst v2)) (EConst (v1 - v2))
| IS_Sub_1 : forall e1 e1' e2,
    istep s e1 e1' ->
    istep s (ESub e1 e2) (ESub e1' e2)
| IS_Sub_2 : forall v1 e2 e2',
    istep s e2 e2' ->
    istep s (ESub (EConst v1) e2) (ESub (EConst v1) e2')
| IS_Mul_0 : forall v1 v2,
    istep s (EMul (EConst v1) (EConst v2)) (EConst (v1 * v2))
| IS_Mul_1 : forall e1 e1' e2,
    istep s e1 e1' ->
    istep s (EMul e1 e2) (EMul e1' e2)
| IS_Mul_2 : forall v1 e2 e2',
    istep s e2 e2' ->
    istep s (EMul (EConst v1) e2) (EMul (EConst v1) e2')
.

Inductive ivalue : expr_int -> Prop :=
| ivalue_const : forall n, ivalue (EConst n).

Theorem istep_progress : forall s e,
  ivalue e \/ exists e', istep s e e'.
Proof.
  intros.
  induction e; [ left | | | | ]; try right.
  - apply ivalue_const.
  - exists (EConst (s x)); apply IS_Var.
  - destruct IHe1 as [ [?] | [? ?] ].
    + destruct IHe2 as [ [?] | [? ?] ].
      * exists (EConst (n + n0)); apply IS_Add_0.
      * exists (EAdd n x); apply IS_Add_2; tauto.
    + exists (EAdd x e2); apply IS_Add_1; tauto.
  - destruct IHe1 as [ [?] | [? ?] ].
    + destruct IHe2 as [ [?] | [? ?] ].
      * exists (EConst (n - n0)); apply IS_Sub_0.
      * exists (ESub n x); apply IS_Sub_2; tauto.
    + exists (ESub x e2); apply IS_Sub_1; tauto.
  - destruct IHe1 as [ [?] | [? ?] ].
    + destruct IHe2 as [ [?] | [? ?] ].
      * exists (EConst (n * n0)); apply IS_Mul_0.
      * exists (EMul n x); apply IS_Mul_2; tauto.
    + exists (EMul x e2); apply IS_Mul_1; tauto.
Qed.

Definition lt_eval (v1 v2 : Z) :=
  if v1 <? v2 then ETrue else EFalse.

Inductive bstep (s : state) : expr_bool -> expr_bool -> Prop :=
| BS_Lt_0 : forall v1 v2,
    bstep s (ELt (EConst v1) (EConst v2)) (lt_eval v1 v2)
| BS_Lt_1 : forall e1 e1' e2,
    istep s e1 e1' ->
    bstep s (ELt e1 e2) (ELt e1' e2)
| BS_Lt_2 : forall v1 e2 e2',
    istep s e2 e2' ->
    bstep s (ELt (EConst v1) e2) (ELt (EConst v1) e2')
| BS_And_False : forall e,
    bstep s (EAnd EFalse e) EFalse
| BS_And_True_True :
    bstep s (EAnd ETrue ETrue) ETrue
| BS_And_True_False :
    bstep s (EAnd ETrue EFalse) EFalse
| BS_And_1 : forall e1 e1' e2,
    bstep s e1 e1' ->
    bstep s (EAnd e1 e2) (EAnd e1' e2)
| BS_And_2 : forall e2 e2',
    bstep s e2 e2' ->
    bstep s (EAnd ETrue e2) (EAnd ETrue e2')
| BS_Not_True :
    bstep s (ENot ETrue) EFalse
| BS_Not_False :
    bstep s (ENot EFalse) ETrue
| BS_Not_1 : forall e1 e1',
    bstep s e1 e1' ->
    bstep s (ENot e1) (ENot e1')
.

Inductive bvalue : expr_bool -> Prop :=
| bvalue_true : bvalue ETrue
| bvalue_false : bvalue EFalse
.

Theorem bstep_progress : forall s e,
  bvalue e \/ exists e', bstep s e e'.
Proof.
  intros.
  induction e; [ left | left | right | right | right ].
  - apply bvalue_true.
  - apply bvalue_false.
  - pose proof (istep_progress s e1); destruct H as [ [?] | [? ?] ].
    + pose proof (istep_progress s e2); destruct H as [ [?] | [? ?] ].
      * exists (lt_eval n n0); apply BS_Lt_0.
      * exists (ELt (EConst n) x); apply BS_Lt_2; tauto.
    + exists (ELt x e2); apply BS_Lt_1; tauto.
  - destruct IHe1 as [ [|] | [? ?] ].
    + destruct IHe2 as [ [|] | [? ?] ].
      * exists ETrue; apply BS_And_True_True.
      * exists EFalse; apply BS_And_True_False.
      * exists (EAnd ETrue x); apply BS_And_2; tauto.
    + exists EFalse; apply BS_And_False.
    + exists (EAnd x e2); apply BS_And_1; tauto.
  - destruct IHe as [ [|] | [? ?] ].
    + exists EFalse; apply BS_Not_True.
    + exists ETrue; apply BS_Not_False.
    + exists (ENot x); apply BS_Not_1; tauto.
Qed.

Definition state_update (s : state) (x : var_name) (v : Z) : state := fun y =>
  if String.eqb x y then v else s y.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
| CS_AsgnStep : forall s x e e',
    istep s e e' ->
    cstep ((CAsgn x e), s) ((CAsgn x e'), s)
| CS_Asgn : forall s x v,
    cstep ((CAsgn x (EConst v)), s) (CSkip, (state_update s x v))
| CS_SeqStep : forall s s' c1 c1' c2,
    cstep (c1, s) (c1', s') ->
    cstep ((CSeq c1 c2), s) ((CSeq c1' c2), s')
| CS_SeqSkip : forall s c,
    cstep ((CSeq CSkip c), s) (c, s)
| CS_IfStep : forall s e e' c1 c2,
    bstep s e e' ->
    cstep ((CIf e c1 c2), s) ((CIf e' c1 c2), s)
| CS_IfTrue : forall s c1 c2,
    cstep ((CIf ETrue c1 c2), s) (c1, s)
| CS_IfFalse : forall s c1 c2,
    cstep ((CIf EFalse c1 c2), s) (c2, s)
| CS_While : forall s e c,
    cstep ((CWhile e c), s) ((CIf e (CSeq c (CWhile e c)) CSkip), s)
.

Inductive cvalue : com -> Prop :=
| cvalue_skip : cvalue CSkip.

Theorem cstep_progress : forall s c,
  cvalue c \/ exists c' s', cstep (c, s) (c', s').
Proof.
  intros.
  induction c; [ left | | | | ]; try right.
  - apply cvalue_skip.
  - pose proof (istep_progress s e); destruct H as [ [?] | [? ?] ].
    + exists CSkip, (state_update s x n); apply CS_Asgn.
    + exists (CAsgn x x0), s; apply CS_AsgnStep; tauto.
  - destruct IHc1 as [ [] | [? [? ?] ] ].
    + exists c2, s; apply CS_SeqSkip.
    + exists (CSeq x c2), x0; apply CS_SeqStep; tauto.
  - pose proof (bstep_progress s e); destruct H as [ [|] | [? ?] ].
    + exists c1, s; apply CS_IfTrue.
    + exists c2, s; apply CS_IfFalse.
    + exists (CIf x c1 c2), s; apply CS_IfStep; tauto.
  - exists (CIf e (CSeq c (CWhile e c)) CSkip), s; apply CS_While.
Qed.


End SmallStep.
