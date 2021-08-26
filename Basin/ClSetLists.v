(* ----------------------------------------------------------------- *)
(*                     Basic algebra of Sets                         *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.
From Practice Require Import Basin.ElemAlg.
From Practice Require Import Basin.ClassicalSets.

Import List.
Import ListNotations.


(* Union: CommMonoid *)
Program Instance magma_union U: Magma _ (@Union U).

Program Instance assoc_union U: Associative _ (@Union U).
Next Obligation. firstorder. Qed.

Program Instance comm_union U: Commutative _ (@Union U).
Next Obligation. firstorder. Qed.

Program Instance hasid_union U: HasIdentity _ (@Union U) := { mid := EmptySet }.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Program Instance semigroup_union U: Semigroup _ (@Union U).
Program Instance monoid_union U: Monoid _ (@Union U).
Program Instance cmon_union U: CommMonoid _ (@Union U).


Program Instance magma_intersect U: Magma _ (@Intersect U).

Program Instance assoc_intersect U: Associative _ (@Intersect U).
Next Obligation. firstorder. Qed.

Program Instance comm_intersect U: Commutative _ (@Intersect U).
Next Obligation. firstorder. Qed.

Program Instance hasid_intersect U: HasIdentity _ (@Intersect U) := { mid := FullSet }.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Program Instance semigroup_intersect U: Semigroup _ (@Intersect U).
Program Instance monoid_intersect U: Monoid _ (@Intersect U).
Program Instance cmon_intersect U: CommMonoid _ (@Intersect U).


Lemma cat_unions_as_unionover: forall U (L: list (ESet U)),
  MCat Union L == MCatOver Union id L.
Proof. move=> U L. by rewrite /MCatOver map_id. Qed.

Lemma cat_intersects_as_intersectover: forall U (L: list (ESet U)),
  MCat Intersect L == MCatOver Intersect id L.
Proof. move=> U L. by rewrite /MCatOver map_id. Qed.


Lemma cat_unionover_compl: forall I U (L: list I) (F: I -> ESet U),
  ~! (MCatOver Union F L) == MCatOver Intersect (fun i => ~! F i) L.
Proof. move=> I U L F. elim: L; firstorder. Qed.

Lemma cat_intersectover_compl: forall I U (L: list I) (F: I -> ESet U),
  ~! (MCatOver Intersect F L) == MCatOver Union (fun i => ~! F i) L.
Proof. move=> I U L F. elim: L => [|a L IH]. firstorder.
  constructor=> x. decides (x :in: F a); firstorder. Qed.


(* Set of lists where each element is in a set *)
Definition ForallSet {U} (T: ESet U): ESet (list U) :=
  mkSet (fun L => Forall (InSet T) L).

(* Set of lists where at least single element is in a set *)
Definition ExistsSet {U} (T: ESet U): ESet (list U) :=
  mkSet (fun L => Exists (InSet T) L).
