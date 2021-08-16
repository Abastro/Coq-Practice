From Practice Require Import Basin.Base.
From Practice Require Import Basin.DecClass.
From Practice Require Import Basin.Sets.

Require Import List.
Import ListNotations.

(* Forall & Exists over list as decidable proposition *)
(* Instance decp1_forall_list {U} (P: U -> Prop) `(DecPred1 U P): DecP1 (Forall P).
Proof with (auto with datatypes).
  intros l. induction l.
  - left...
  - destruct (H a), IHl;
    [left | right | right | right]...
    all: now inversion 1.
Qed.

Instance decp1_exists_list {U} (P: U -> Prop)  `(DecPred1 U P): DecP1 (Exists P).
Proof with (auto with datatypes).
  intros l. induction l.
  - right. now inversion 1.
  - destruct (H a), IHl;
    [left | left | left | right]...
    now inversion 1.
Qed. *)

(* Set of lists where each element is in a set *)
Definition ForallSet {U} (T: ESet U): ESet (list U) :=
  mkSet (fun L => Forall (InSet T) L).

(* Set of lists where at least single element is in a set *)
Definition ExistsSet {U} (T: ESet U): ESet (list U) :=
  mkSet (fun L => Exists (InSet T) L).


(* Union/Intersection over list *)
Fixpoint UnionList {U} (l: list (ESet U)): ESet U :=
  match l with
  | nil => EmptySet
  | A :: l' => A \\// UnionList l'
  end.

Fixpoint IntersectList {U} (l: list (ESet U)): ESet U :=
  match l with
  | nil => FullSet
  | A :: l' => A //\\ IntersectList l'
  end.

Lemma UnionList_couple: forall U (A B: ESet U),
  UnionList [A; B] == A \\// B.
Proof. intros. unfold UnionList. firstorder. Qed.

Lemma IntersectList_couple: forall U (A B: ESet U),
  IntersectList [A; B] == A //\\ B.
Proof. intros. unfold IntersectList. firstorder. Qed.

Lemma UnionList_app: forall U (L1 L2: list (ESet U)),
  UnionList (L1 ++ L2) == UnionList L1 \\// UnionList L2.
Proof. intros. induction L1; firstorder. Qed.

Lemma IntersectList_app: forall U (L1 L2: list (ESet U)),
  IntersectList (L1 ++ L2) == IntersectList L1 //\\ IntersectList L2.
Proof. intros. induction L1; firstorder. Qed.

#[export]
Hint Unfold UnionList IntersectList: sets.
#[export]
Hint Resolve UnionList_app IntersectList_app: sets.
