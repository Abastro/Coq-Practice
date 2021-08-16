Require Import Orders.
Require Import OrdersTac.

From Practice Require Import Basin.Base.
From Practice Require Import Basin.ClassicalSets.

Module Type PartialOrder := StrOrder <+ HasLe <+ LeIsLtEq.

(* ----------------------------------------------------------------- *)

Module InfSup (Import O: UsualTotalOrder').
Module OF := OrderFacts O O. Import OF.
Module MOT := MakeOrderTac O O. Import MOT.

Definition U := O.t.

Inductive Direction : Type :=
  | LT | GT.
Definition dnot (d: Direction) : Direction :=
  match d with
  | LT => GT | GT => LT end.
Definition ord_dir (d: Direction) : U -> U -> Prop :=
  match d with
  | LT => le
  | GT => flip le
  end.
Definition ord_str_dir (d: Direction) : U -> U -> Prop :=
  match d with
  | LT => lt
  | GT => flip lt
  end.
Notation "x '[!' d '!]' y" := (ord_dir d x y) (at level 60).
Notation "x '<!' d '!>' y" := (ord_str_dir d x y) (at level 60).

Ltac order_dir d := destruct d; unfold ord_dir in *; unfold flip in *; order.

Property dord_ref: forall d a, a [!d!] a.
Proof. order_dir d. Qed.
Property dord_trans: forall d a b c, a [!d!] b -> b [!d!] c -> a [!d!] c.
Proof. order_dir d. Qed.
Property dord_antisym: forall d a b, a [!d!] b -> b [!d!] a -> a = b.
Proof. order_dir d. Qed.
Property dnot_sym: forall d a b, b [!dnot d!] a <-> a [!d!] b.
Proof. destruct d; unfold dnot; unfold ord_dir; tauto. Qed.

Instance PreOrder d: PreOrder (ord_dir d).
Proof. split.
  - unfold Reflexive. apply dord_ref.
  - unfold Transitive. apply dord_trans.
Qed.
(* Not proving partial order, too complex definition *)
Instance Antisymmetric d: Antisymmetric _ eq (ord_dir d).
Proof. unfold Antisymmetric. apply dord_antisym. Qed.

#[export]
Hint Constructors Direction: ordered_type.
#[export]
Hint Unfold dnot ord_dir ord_str_dir: ordered_type.
#[export]
Hint Resolve dord_ref dord_trans dord_antisym: ordered_type.
#[export]
Hint Resolve <- dnot_sym: ordered_type.
#[export]
Hint Resolve -> dnot_sym: ordered_type.

(* ----------------------------------------------------------------- *)

Section Directed.
Variable d: Direction.

Section Single.
Variable A: ESet U.

Definition Bound b: Prop := 
  forall x, x :in: A -> b [!d!] x.
Definition Extremum m: Prop :=
  m :in: A /\ Bound m.


Definition Bounded_D: Prop :=
  exists b, Bound b.
Definition Extr : Type :=
  {m | unique Extremum m}.

End Single.

(* Encapsulation of Bound as a ESet *)
Definition Bnds (A: ESet U): ESet U :=
  mkSet (fun b => Bound A b).
Definition Range_inc (a: U): ESet U :=
  mkSet (fun x => a [!d!] x).
Definition Range_exc (a: U): ESet U :=
  mkSet (fun x => a <!d!> x).


(* Bnds properties *)
Property bnds_iff: forall A b, b :in: Bnds A <-> Bound A b.
Proof. easy. Qed.

(* Range properties *)
Property range_inc_iff: forall a x, x :in: Range_inc a <-> a [!d!] x.
Proof. easy. Qed.
Property range_exc_iff: forall a x, x :in: Range_exc a <-> a <!d!> x.
Proof. easy. Qed.


Property range_incl: forall a, a :in: Range_inc a.
Proof. intros. apply range_inc_iff. order_dir d. Qed.
Property range_incl_extreme: forall a, Extremum (Range_inc a) a.
Proof. intros. split. apply range_incl. easy. Qed.
Property range_inc_include_iff: forall a b,
  a [!d!] b <-> Range_inc a =:> Range_inc b.
Proof.
  intros. unfold Include.
  split; setoid_rewrite range_inc_iff; eauto with ordered_type.
Qed.

End Directed.

Definition Bounded A := Bounded_D LT A /\ Bounded_D GT A.

Definition Minimum := Extremum LT.
Definition Maximum := Extremum GT.

(* Supremum and Infimum *)
Definition Limfemum (d: Direction) (A: ESet U) (s: U) : Prop :=
  Extremum (dnot d) (Bnds d A) s.
Definition Infimum := Limfemum LT.
Definition Supremum := Limfemum GT.

Definition Limf (d: Direction) (A: ESet U): Type :=
  {s | unique (Limfemum d A) s}.

Notation "[' a '|" := (Range_inc LT a).
Notation "|' a ']" := (Range_inc GT a).
Notation "(' a '|" := (Range_exc LT a).
Notation "|' a ')" := (Range_exc GT a).

Definition Interval (incl_a incl_b: bool) (a b: U) :=
  match incl_a, incl_b with
  | true, true => [' a '| //\\ |' b ']
  | true, false => [' a '| //\\ |' b ')
  | false, true => (' a '| //\\ |' b ']
  | false, false => (' a '| //\\ |' b ')
  end.

Notation "[' a , b ']" := (Interval true true a b).
Notation "[' a , b ')" := (Interval true false a b).
Notation "(' a , b ']" := (Interval false true a b).
Notation "(' a , b ')" := (Interval false false a b).

(* Hints and morphisms *)
#[export]
Hint Unfold Bound Extremum Bounded_D Extr Bounded Minimum Maximum
  Limfemum Supremum Infimum Interval: ordered_type.
#[export]
Hint Immediate range_incl: ordered_type.
#[export]
Hint Resolve -> bnds_iff range_inc_iff range_exc_iff range_inc_include_iff: ordered_type.
#[export]
Hint Resolve <- bnds_iff range_inc_iff range_exc_iff range_inc_include_iff: ordered_type.
#[export]
Hint Resolve range_incl_extreme: ordered_type.

Add Parametric Morphism: Bound
  with signature Logic.eq ==> equiv ==> Logic.eq ==> iff as bound_mor.
Proof. unfold Bound. intros. rw_refl. Qed.
Add Parametric Morphism: Extremum
  with signature Logic.eq ==> equiv ==> Logic.eq ==> iff as ext_mor.
Proof. unfold Extremum. intros. rw_refl. Qed.
Add Parametric Morphism: Bounded_D
  with signature Logic.eq ==> equiv ==> iff as bddd_mor.
Proof. unfold Bounded_D. intros. rw_refl. Qed.

Add Parametric Morphism : Bnds
  with signature Logic.eq ==> equiv ==> equiv as bnd_mor.
Proof. intros ** ?. unfold Bnds, InSet. rw_refl. Qed.
Add Parametric Morphism : Bounded
  with signature equiv ==> iff as bdd_mor.
Proof. unfold Bounded. intros. rw_refl. Qed.
Add Parametric Morphism : Limfemum
  with signature Logic.eq ==> equiv ==> Logic.eq ==> iff as limf_mor.
Proof. unfold Limfemum. intros. rw_refl. Qed.

(* ----------------------------------------------------------------- *)

Lemma bound_equiv_in_range: forall d A b,
  Bound d A b <-> A <:= Range_inc d b.
Proof. unfold Bound, Include. setoid_rewrite range_inc_iff. reflexivity. Qed.

Lemma bnds_contains_op_range: forall d A b,
  b :in: Bnds d A -> Bnds d A =:> Range_inc (dnot d) b.
Proof. unfold Include. intros * H x.
  rewrite bnds_iff, bound_equiv_in_range in *.
  etransitivity; eauto with ordered_type. Qed.

Lemma bnds_in_op_range: forall d A a,
  a :in: A -> Bnds d A <:= Range_inc (dnot d) a.
Proof. unfold Include. intros. auto with ordered_type. Qed.

Lemma bnds_included: forall d A B, A =:> B -> Bnds d A <:= Bnds d B.
Proof. unfold Include. intros. auto with ordered_type. Qed.

(* set union ~> bounds intersection *)
Lemma bnds_union: forall d A B, Bnds d (A \\// B) == Bnds d A //\\ Bnds d B.
Proof. intros ** ?.
  rewrite intersect_iff, 3 bnds_iff. firstorder. Qed.


Property extremum_unique: forall d A, uniqueness (Extremum d A).
Proof.
  unfold uniqueness, Extremum. intros * [HI HB] [HI' HB'].
  assert (H: x [!d!] y /\ y [!d!] x) by (split; auto with ordered_type).
  eauto with ordered_type.
Qed.
Corollary ext_unique_find: forall d A s, Extremum d A s -> Extr d A.
Proof. intros. exists s. apply unique_by_uniqueness; auto using extremum_unique. Qed.

Corollary infsup_unique: forall d A, uniqueness (Limfemum d A).
Proof. unfold Limfemum. intros. apply extremum_unique. Qed.
Corollary infsup_unique_find: forall d A s, Limfemum d A s -> Limf d A.
Proof. intros. exists s. apply unique_by_uniqueness; auto using infsup_unique. Qed.


Lemma extremum_included: forall d A B (mA: Extr d A) (mB: Extr d B),
  A =:> B -> get mA [!d!] get mB.
Proof. intros ? ? ? (mA & [IA BA] & ?) (mB & [IB BB] & ?) H.
  auto with ordered_type. Qed.

Lemma extremum_union: forall d A B (mA: Extr d A) (mB: Extr d B),
  get mA [!d!] get mB -> Extremum d (A \\// B) (get mA).
Proof with (eauto with sets ordered_type).
  intros ? ? ? (mA & [IA BA] & ?) (mB & [IB BB] & ?) H. simpl in *.
  split. auto... intros ? [|]... Qed.


Property interval_incl_edge: forall a b,
  a <= b -> (a :in: [' a, b ']) /\ (b :in: [' a, b ']).
Proof. unfold Interval. split; constructor; auto with ordered_type. Qed.
Property interval_min_max: forall a b,
  a <= b -> Minimum [' a, b '] a /\ Maximum [' a, b '] b.
Proof with trivial.
  split. do 2 red.
  all: split; [apply interval_incl_edge|]...
  all: apply bound_equiv_in_range; firstorder.
Qed.


#[export]
Hint Resolve -> bound_equiv_in_range: ordered_type.
#[export]
Hint Resolve <- bound_equiv_in_range: ordered_type.
#[export]
Hint Resolve bnds_contains_op_range bnds_in_op_range bnds_included bnds_union
  extremum_unique infsup_unique extremum_included extremum_union: ordered_type.


Property range_inc_bound: forall d a,
  Bnds d (Range_inc d a) == Range_inc (dnot d) a.
Proof. intros. apply same_inc_iff. split; auto with ordered_type. Qed.

Property range_inc_infsup: forall d a, Limfemum d (Range_inc d a) a.
Proof. intros. unfold Limfemum.
  rewrite range_inc_bound. apply range_incl_extreme. Qed.


(* Infimum/Supremum exists iff the bound is given as an inclusive range. *)
Proposition infsup_gives_bnds_range: forall d (A: ESet U) s,
  Limfemum d A s <-> Bnds d A == Range_inc (dnot d) s.
Proof with (auto with ordered_type).
  unfold Limfemum, Extremum. split.
  - (* -> *) intros [HI HB]. apply same_inc_iff. split...
  - (* <- *) intros ->...
Qed.
Corollary bnds_to_range_limf: forall d (A: ESet U) (lA: Limf d A),
  Bnds d A == Range_inc (dnot d) (get lA).
Proof. intros. apply infsup_gives_bnds_range, (getPr lA). Qed.


Proposition extremum_is_infsup: forall d (A: ESet U) (mA: Extr d A),
  Limfemum d A (get mA).
Proof. intros. destruct (getPr mA) as [[] _]. split; auto with ordered_type. Qed.


Lemma infsup_included: forall d A B (lA: Limf d A) (lB: Limf d B),
  A =:> B -> get lA [!d!] get lB.
Proof. intros * H. rewrite <- dnot_sym. apply range_inc_include_iff.
  rewrite <-2 bnds_to_range_limf. auto with ordered_type. Qed.

Lemma infsup_union: forall d A B (lA: Limf d A) (lB: Limf d B),
  get lA [!d!] get lB -> Limfemum d (A \\// B) (get lA).
Proof. intros * H %dnot_sym %range_inc_include_iff.
  apply infsup_gives_bnds_range. rewrite <-2 bnds_to_range_limf in *.
  firstorder. Qed.

#[export]
Hint Resolve range_inc_bound bnds_to_range_limf extremum_is_infsup
  infsup_included infsup_union: ordered_type.
#[export]
Hint Resolve -> infsup_gives_bnds_range: ordered_type.
#[export]
Hint Resolve <- infsup_gives_bnds_range: ordered_type.


(* Completeness *)
Definition Complete : Type := forall d (A: ESet U), Bounded_D d A -> Limf d A.

End InfSup.
