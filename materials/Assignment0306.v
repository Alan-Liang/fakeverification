Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Import SetsNotation.
Require Import PV.Syntax.
Import Lang_While.
Require Import PV.PracticalDenotations.
Import DntSem_While.
Require Import PV.EquivAndRefine.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.
Arguments Rels.id: simpl never.
Arguments Rels.concat: simpl never.
Arguments Sets.indexed_union: simpl never.

(** 习题：*)
Theorem Rels_concat_empty_r:
  forall {A B: Type} (x: A -> B -> Prop),
    x ∘ ∅ == ∅.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)
Theorem CSeq_CSkip: forall c,
  [[ c; skip ]] ~=~ c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)
Theorem CSkip_CSeq: forall c,
  [[ skip; c ]] ~=~ c.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 习题：*)
Theorem CWhile_unroll_nrm: forall (e: expr) (c: com),
  ⟦ if e then { c ; while (e) do {c} } else { skip } ⟧.(nrm) ==
  ⟦ while (e) do {c} ⟧.(nrm).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


