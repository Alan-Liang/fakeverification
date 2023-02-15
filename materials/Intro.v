Require Import Coq.Setoids.Setoid.






(** * Coq证明的例子 *)

(** 这是一个关于群论的证明。首先，我们要定义一个群包含哪些运算。*)

Class GroupOperator: Type := {
  carrier_set: Type;
  zero: carrier_set;
  add: carrier_set -> carrier_set -> carrier_set;
  neg: carrier_set -> carrier_set
}.

(** 这里我们可以忽略_[Class]_、_[Type]_这些Coq保留字，上面这个定义大致说的是：要
    定义群运算就先要定义一个集合（_[carrier_set]_)，之后一个群应当包含一个单位元
    （_[zero]_）、一个二元运算（_[add]_）以及一个逆元预算（_[neg]_）。*)

Notation "0" := (zero).
Notation "x + y" := (add x y).
Notation "- x" := (neg x).

(** 在Coq中，我们可以用零、加号以及负号这些Notation来帮助我们表述相关性质。例
    如：下面就是一个合法的关于群论的命题：*)

Check forall (G: GroupOperator) (x y: carrier_set), x + y = y + x.

(** 这里Coq的Check指令可以理解为检查一个表述语法上是否合法。上面检查的结果是：这
    是一个合法的Coq命题。注意，这只是语法检查，不是证明。下面是群论中的经典证
    明：从左单位元、左逆元两条性质推出右逆元性质。首先定义：一个群应当具有左单位
    元、左逆元与结合律这三条性质。*)

Class GroupProperties (G: GroupOperator): Prop := {
  assoc: forall (x y z: carrier_set), (x + y) + z = x + (y + z);
  left_unit: forall (x: carrier_set), 0 + x = x;
  left_inv: forall (x: carrier_set), add (neg x) x = zero
}.

(** 其次证明：有上面性质可以推出右逆元性质。*)

Theorem right_inv {G: GroupOperator} {GP: GroupProperties G}:
  (forall (x: carrier_set), x + (- x) = 0).
Proof.

(** 在CoqIDE中，你可以用Ctrl+向下快捷键让Coq检验你的定义与证明。通过检验的代码会
    变成绿色。进入证明模式后，你会在CoqIDE的右边窗口看到现在所有剩余的证明目标。
    例如，你现在可以看到以下证明目标：*)

(** G : GroupOperator
    GP : GroupProperties G
    ============================
    forall x : carrier_set, x + - x = 0 *)

(** 这里横线上方的是目前可以使用的前提，横线下方的是目前要证明的结论。接下去的每
    一行都是一条证明指令（tactic），每条证明指令可以将一个证明目标规约为0个，1个
    或者更多的证明目标。*)

  intros x.

  (** 下面的rewrite指令可以把待证明结论中的项替换为与一个等价的项。在下面的第一
      条rewrite指令表示将_[left_unit]_性质的第一个参数代入为_[x + (- x)]_后进行
      替换。因此，待证明结论就变为了_[0 + (x + (- x)) = 0]_。*)

  rewrite <- (left_unit (x + (- x))).

  (** 下面这条指令中，通过rewrite指令后的箭头表明了替换的方向为使用_[left_inv]_
      等式的左侧替换该等式的右侧。而指令最后的at 1则表示只对第一个可以替换处进行
      替换。*)

  rewrite <- (left_inv (- x)) at 1.

  (** 在没有歧义的情况下，并不一定需要填写参数。*)

  rewrite -> assoc.
  rewrite <- (assoc (- x)).

  (** 如果不使用箭头，则默认为使用向右的箭头。*)

  rewrite left_inv.
  rewrite left_unit.
  rewrite left_inv.

  (** 最后，reflexivity指令说的是：等式具有自反性，现在等式两边完全相同，所以已
      经证明完了。 *)

  reflexivity.
Qed.

(** 下面可以进一步证明右单位元性质。*)

Theorem right_unit {G: GroupOperator} {GP: GroupProperties G}:
  forall (x: carrier_set), x + 0 = x.
Proof.
  intros.
  rewrite <- (left_inv x).
  rewrite <- assoc.

  (** 证明中可以使用先前证明的结论。*)

  rewrite right_inv.
  rewrite left_unit.
  reflexivity.
Qed.

(** 我们还可以证明双重取逆符号的消去。*)

Theorem inv_involutive {G: GroupOperator} {GP: GroupProperties G}:
  forall (x: carrier_set), - - x = x.
Proof.
  intros.
  rewrite <- (left_unit (- - x)).
  rewrite <- (right_inv x).
  rewrite assoc.

  (** 在Coq中，也可以将多条rewrite指令，写到一起。*)

  rewrite right_inv, right_unit.
  reflexivity.
Qed.

(** 习题：*)
Lemma cancel_PN {G: GroupOperator} {GP: GroupProperties G}:
  forall (x y: carrier_set), x + y + - y = x.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  rewrite assoc, right_inv, right_unit.
  reflexivity.
Qed.

(** 在Coq中，_[rewrite]_指令除了可以使用通过_[Class]_单独列出的假设以及已经证明
    的结论还可以使用待证明目标中的前提假设。下面命题说的是，在一个群中，如果
    _[x + z = y + z]_那么_[x = y]_。*)
Lemma cancel_right {G: GroupOperator} {GP: GroupProperties G}:
  forall (x y z: carrier_set),
    x + z = y + z ->
    x = y.
Proof.
  intros.

  (** 经过_[intros]_之后，_[x + z = y + z]_这一前提被命名为_[H]_。 *)

  rewrite <- (right_unit x), <- (right_unit y).
  rewrite <- (right_inv z).
  rewrite <- ! assoc.

  (** 下面指令利用前提_[H]_进行_[rewrite]_。 *)

  rewrite H.
  reflexivity.
Qed.

(** 习题：*)
Lemma move_right_PN {G: GroupOperator} {GP: GroupProperties G}:
  forall (x y z: carrier_set),
    x + z = y ->
    x = y + - z.
(* 请在此处填入你的证明，以_[Qed]_结束。 *)
Proof.
  intros.
  rewrite <- H.
  rewrite cancel_PN.
  reflexivity.
Qed.








