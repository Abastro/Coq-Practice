(* ----------------------------------------------------------------- *)
(*                        Elementary Algebra                         *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.
Require Import Permutation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.


(* ----------------------------------------------------------------- *)
(*                       Equivalence on list                         *)
(* ----------------------------------------------------------------- *)

(* Equivalence on list *)
Instance equiv_list U `(D: Setoid U): Equivalence (Forall2 equiv).
Proof with eauto.
  split; red.
  - (* Reflexivity *)
    elim=> [|a x' IH]; constructor...
  - (* Symmetry *)
    move=> x y. elim=> []...
  - (* Transitivity *)
    move=> x y + H.
    elim: H => [|hx hy x' y' E Hxy IH] z Hy...
    inversion Hy; subst. constructor...
Qed.

(* Setoid on list required *)
Instance setoid_list U `(D: Setoid U): Setoid (list U) := {
  equiv := Forall2 equiv
}.

Add Parametric Morphism U `(Setoid U): (@app U)
  with signature equiv ==> equiv ==> equiv as app_mor.
Proof with auto.
  move=> l1 l2.
  elim=> [|h1 h2 l1' l2' Eh El IH] m1 m2 Em...
  simpl. constructor... by apply: IH.
Qed.


(* ----------------------------------------------------------------- *)
(*               Elementary Algebra on single operator               *)
(* ----------------------------------------------------------------- *)

Create HintDb alg discriminated.

Definition Operator U: Type := U -> U -> U.


Section Op.
Context {U} `(D: Setoid U) (op: Operator U).

Class Magma: Type := {
  op_proper: Proper (equiv ==> equiv ==> equiv) op
}.

Local Add Parametric Morphism `(Magma): op
  with signature equiv ==> equiv ==> equiv as mop_mor.
Proof. apply op_proper. Qed.

Local Infix "@" := op (at level 25, left associativity).

Class Associative: Prop :=
  associativity: forall x y z, x @ (y @ z) == (x @ y) @ z.
Class Commutative: Prop :=
  commutativity: forall x y, x @ y == y @ x.
Class HasIdentity: Type := {
  mid: U
; mid_left: forall x, mid @ x == x
; mid_right: forall x, x @ mid == x
}.


Class Semigroup: Type := {
  sem_mag :> Magma
; sem_assoc :> Associative
}.

Class Monoid: Type := {
  mon_sem :> Semigroup
; mon_hasid :> HasIdentity
}.

Class CommMonoid: Type := {
  cm_mon :> Monoid
; cm_comm :> Commutative
}.


(* Semigroup concatenation with starting element on right *)
Definition SCatWith `{S: Semigroup} (d: U) (l: list U): U :=
  fold_right op d l.

Add Parametric Morphism `(Semigroup): (@SCatWith _)
  with signature equiv ==> equiv ==> equiv as scatwith_mor.
Proof.
  move=> a b E x y.
  elim=> {x y} [|hx hy x' y' Hh _ IH] //=.
  rewrite Hh IH. auto.
Qed.

Lemma scatwith_app: forall `(Semigroup) d e l1 l2,
  SCatWith d l1 @ SCatWith e l2 == SCatWith e (l1 ++ d :: l2).
Proof.
  move=> ? d e l1 l2.
  elim: l1 => [|h l1' IH] /=; auto.
  rewrite <- associativity. rw_refl.
Qed.


(* Monoid concatenation *)
Definition MCat `{M: Monoid} (l: list U): U :=
  fold_right op mid l.

Add Parametric Morphism `(Monoid): (@MCat _)
with signature equiv ==> equiv as mcat_mor.
Proof.
  move=> x y. elim=> {x y} [|hx hy x' y' Hh Hl IH] //=.
  all: rw_refl.
Qed.


Lemma mcat_nil: forall `(Monoid),
  MCat [] == mid.
Proof. reflexivity. Qed.

Lemma mcat_app: forall `(Monoid) (l1 l2: list U),
  MCat l1 @ MCat l2 == MCat (l1 ++ l2).
Proof.
  move=> ? l1 l2. elim: l1 => [|h l1' IH] /=.
  - apply: mid_left.
  - rewrite <- associativity. rw_refl.
Qed.

Lemma mcat_single: forall `(Monoid) a,
  MCat [a] == a.
Proof. move=> > /=. apply: mid_right. Qed.

Lemma mcat_couple: forall `(Monoid) a b,
  MCat [a; b] == a @ b.
Proof. move=> > /=. rewrite mid_right. reflexivity. Qed.

(* Induction on mcat *)
Lemma mcat_ind: forall `(Monoid) (l: list U) (P: U -> Prop),
  P mid -> (forall a b, P a -> P b -> P (a @ b)) ->
  Forall P l -> P (MCat l).
Proof.
  move=> M l P Hid Hop.
  elim=> {l} [|x l' Hx Hl' IH] //=.
  by apply: Hop.
Qed.

(* Commutative monoid -> Can permutate *)
Lemma mcat_perm: forall `(CommMonoid) (l m: list U),
  Permutation l m -> MCat l == MCat m.
Proof with eauto.
  move=> C l m. elim=> {l m} [| a l m HP IH | a b l |] /=...
  - rw_refl.
  - rewrite !associativity (commutativity a)...
Qed.

Definition MCatOver {V} `{M: Monoid} (f: V -> U) (l: list V): U :=
  MCat (map f l).


End Op.

Arguments mid {U D} op {HasIdentity}.
Arguments SCatWith {U D} op {S}.
Arguments MCat {U D} op {M}.
Arguments MCatOver {U D} op {V M}.

#[export]
Hint Resolve associativity commutativity mid_left mid_right
  scatwith_app
  mcat_nil mcat_app mcat_perm: alg.



(* ----------------------------------------------------------------- *)
(*                          El. Alg. Examples                        *)
(* ----------------------------------------------------------------- *)

(* List: monoid *)
Program Instance magma_list U `(Setoid U): Magma _ (@app U).

Program Instance assoc_app U `(Setoid U): Associative _ (@app U).
Next Obligation. rewrite app_assoc. reflexivity. Qed.

Program Instance hasid_app U `(Setoid U): HasIdentity _ (@app U) := { mid := [] }.
Next Obligation. reflexivity. Qed.
Next Obligation. rewrite app_nil_r. reflexivity. Qed.

Program Instance semigroup_app U `(Setoid U): Semigroup _ (@app U).
Program Instance monoid_app U `(Setoid U): Monoid _ (@app U).


(* Nat add: commutative monoid *)
Program Instance magma_nat_add: Magma _ Nat.add.

Program Instance assoc_nat_add: Associative _ Nat.add.
Next Obligation. apply Nat.add_assoc. Qed.

Program Instance comm_nat_add: Commutative _ Nat.add.
Next Obligation. apply Nat.add_comm. Qed.

Program Instance hasid_nat_add: HasIdentity _ Nat.add := { mid := 0 }.

Program Instance semigroup_nat_add: Semigroup _ Nat.add.
Program Instance monoid_nat_add: Monoid _ Nat.add.
Program Instance cmon_nat_add: CommMonoid _ Nat.add.


(* Nat mul: commutative monoid *)
Program Instance magma_nat_mul: Magma _ Nat.mul.

Program Instance assoc_nat_mul: Associative _ Nat.mul.
Next Obligation. apply Nat.mul_assoc. Qed.

Program Instance comm_nat_mul: Commutative _ Nat.mul.
Next Obligation. apply Nat.mul_comm. Qed.

Program Instance hasid_nat_mul: HasIdentity _ Nat.mul := { mid := 1 }.
Next Obligation. apply Nat.mul_1_r. Qed.

Program Instance semigroup_nat_mul: Semigroup _ Nat.mul.
Program Instance monoid_nat_mul: Monoid _ Nat.mul.
Program Instance cmon_nat_mul: CommMonoid _ Nat.mul.
