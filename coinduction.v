CoInductive colist (A: Type) : Type :=
  | conil : colist A
  | cocons : A -> colist A -> colist A.

CoFixpoint from (n: nat) : colist nat := cocons nat n (from (1 + n)).

CoInductive Infinite A : colist A -> Prop :=
  | Inf : forall x l, Infinite A l -> Infinite A (cocons A x l).

Inductive list (A: Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Inductive Finite A : list A -> Prop :=
  | Fin : forall x l, Finite A l -> Finite A (cons A x l)
  | FinNil : Finite A (nil A).

Fixpoint to (n: nat) : list nat := match n with
  | O => nil nat
  | (S n') => cons nat n (to n')
end.

Theorem to_eq : forall (n: nat), (to n) = match n with
  | O => nil nat
  | (S n') => cons nat n (to n')
end.
destruct n; reflexivity.
Qed.

Example test:
  forall (n: nat), Finite nat (to n).
Proof.
  fix H 1.
  intros.
  rewrite to_eq.
  destruct n.
  - constructor.
  - constructor.
    apply H.
Qed.

Definition frob A (s : colist A) : colist A :=
  match s with
    | (cocons _ h t) => cocons A h t
    | (conil _) => conil A
  end.

Theorem frob_eq : forall A (s : colist A), s = frob A s.
destruct s; reflexivity.
Qed.

Example cotest:
  forall (n: nat), Infinite nat (from n).
Proof.
  cofix H.
  intros.
  rewrite (frob_eq nat (from n)).
  simpl.
  constructor.
  apply H.
Qed.
