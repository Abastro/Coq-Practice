(* ----------------------------------------------------------------- *)
(*                         Classical Sets                            *)
(*                                                                   *)
(*  Classical sets assuming Law of excluded middle.                  *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Basin.Base.


Axiom excluded_middle: forall P: Prop, P \/ ~P.

Tactic Notation "decides" constr(x) :=
  destruct (excluded_middle x).
Tactic Notation "decides" constr(x) "as" simple_intropattern(y) :=
  destruct (excluded_middle x) as y.

Ltac contra := match goal with
  | [ |- ?R ] => let c := fresh "contra" in decides R as [|c]; [easy | exfalso]
  end.


Generalizable All Variables.

(* ----------------------------------------------------------------- *)
(*                            Set definition                         *)
(* ----------------------------------------------------------------- *)

Record ESet (U:Type): Type := mkSet{ InSet: U -> Prop }.

Arguments mkSet {U}.
Arguments InSet {U}.

Section ESetDef.
Context {U:Type}.

Property mkSet_In: forall (P: U -> Prop), InSet (mkSet P) = P.
Proof. reflexivity. Qed.

Inductive SameSet (A B: ESet U): Prop :=
  same_set: (forall x: U, InSet A x <-> InSet B x) -> SameSet A B.

Property SameSet_iff: forall (A B: ESet U),
  SameSet A B <-> (forall x: U, InSet A x <-> InSet B x).
Proof. firstorder. Qed.

End ESetDef.


Notation "x ':in:' A" := (InSet A x) (at level 70, no associativity).

Instance equiv_sameset U: Equivalence (@SameSet U).
Proof. split; red; setoid_rewrite SameSet_iff;
  [ reflexivity | symmetry | etransitivity]; eauto. Qed.

Program Instance setoid_set U: Setoid (ESet U) := {
  equiv := SameSet }.

Property set_eq_iff: forall U (A B: ESet U),
  A == B <-> (forall x: U, x :in: A <-> x :in: B).
Proof. firstorder. Qed.


Add Parametric Morphism U: (@InSet U)
  with signature equiv ==> eq ==> iff as in_mor.
Proof. move=> >. by move/set_eq_iff=> ?. Qed.


Section ESetBasics.
Context {U:Type}.

Definition Include (B C: ESet U): Prop := forall x, x :in: B -> x :in: C.

Definition EmptySet: ESet U := mkSet (const False).
Definition FullSet: ESet U := mkSet (const True).

Definition Intersect (B C: ESet U): ESet U := mkSet (fun x => x :in: B /\ x :in: C).
Definition Union (B C: ESet U): ESet U := mkSet (fun x => x :in: B \/ x :in: C).
Definition Complement (B: ESet U): ESet U := mkSet (fun x => ~ x :in: B).
Definition Setminus (B C: ESet U): ESet U := mkSet (fun x => x :in: B /\ ~ x :in: C).

Definition Singleton `{Setoid U} (x: U): ESet U := mkSet (fun y => x == y).

Inductive Inhabited (B: ESet U): Prop :=
  intro_inhabit: forall x, x :in: B -> Inhabited B.

End ESetBasics.

Instance preorder_inc U: PreOrder (@Include U).
Proof. split; firstorder. Qed.


Notation "'{{' x '}}'" := (Singleton x) (at level 0).
Notation "'{{' x , .. , y , z '}}'" :=
  (Union (Singleton x) .. (Union (Singleton y) (Singleton z)) ..)
  (at level 0, no associativity).
Notation "A '//\\' B" := (Intersect A B) (at level 55, right associativity).
Notation "A '\\//' B" := (Union A B) (at level 60, right associativity).
Notation "'~!' A" := (Complement A) (at level 20).
Notation "A '\\' B" := (Setminus A B) (at level 65, left associativity).

Notation "A '<:=' B" := (Include A B) (at level 70, no associativity).
Notation "A '=:>' B" := (Include B A) (at level 70, no associativity).

Add Parametric Morphism U: (@Include U)
  with signature equiv ==> equiv ==> iff as inc_mor.
Proof. firstorder. Qed.
Add Parametric Morphism U: (@Intersect U)
  with signature equiv ==> equiv ==> equiv as intersect_mor.
Proof. firstorder. Qed.
Add Parametric Morphism U: (@Union U)
  with signature equiv ==> equiv ==> equiv as union_mor.
Proof. firstorder. Qed.
Add Parametric Morphism U: (@Complement U)
  with signature equiv ==> equiv as compl_mor.
Proof. firstorder. Qed.
Add Parametric Morphism U: (@Setminus U)
  with signature equiv ==> equiv ==> equiv as setminus_mor.
Proof. firstorder. Qed.

Add Parametric Morphism U `(Setoid U): (@Singleton U _)
  with signature equiv ==> equiv as single_mor.
Proof. move=> *. constructor=> x /=. rw_refl. Qed.
Add Parametric Morphism U: (@Inhabited U)
  with signature equiv ==> iff as inhabit_mor.
Proof. firstorder. Qed.

#[export]
Hint Unfold InSet Include: sets.

(* ----------------------------------------------------------------- *)
(*                      Set Operation Properties                     *)
(* ----------------------------------------------------------------- *)

Section SetOps.
Context {U:Type}.

Lemma same_inc_iff: forall (A B: ESet U),
  (A <:= B /\ A =:> B) <-> A == B.
Proof. firstorder. Qed.

(* iff properties for rewriting *)
Property union_iff: forall (B C: ESet U) x,
  x :in: B \\// C <-> x :in: B \/ x :in: C.
Proof. firstorder. Qed.
Property intersect_iff: forall (B C: ESet U) x,
  x :in: B //\\ C <-> x :in: B /\ x :in: C.
Proof. firstorder. Qed.
Property compl_iff: forall (A: ESet U) x,
  x :in: ~! A <-> ~ x :in: A.
Proof. firstorder. Qed.
Property setminus_iff: forall (B C: ESet U) x,
  x :in: B \\ C <-> x :in: B /\ ~ x :in: C.
Proof. firstorder. Qed.
Property singleton_iff: forall `(Setoid U) (x y: U),
  y :in: {{ x }} <-> x == y.
Proof. firstorder. Qed.

Lemma inc_empty: forall (A: ESet U), A =:> EmptySet.
Proof. firstorder. Qed.
Lemma inc_full: forall (A: ESet U), A <:= FullSet.
Proof. firstorder. Qed.

(* Union, Intersection *)

Lemma union_comm: forall B C: ESet U, B \\// C == C \\// B.
Proof. firstorder. Qed.
Lemma union_assoc: forall A B C: ESet U, (A \\// B) \\// C == A \\// (B \\// C).
Proof. firstorder. Qed.

Property intersect_comm: forall B C: ESet U, B //\\ C == C //\\ B.
Proof. firstorder. Qed.
Property intersect_assoc: forall A B C: ESet U, (A //\\ B) //\\ C == A //\\ (B //\\ C).
Proof. firstorder. Qed.

Property union_inc: forall B C: ESet U, B <:= B \\// C.
Proof. firstorder. Qed.
Property union_inc2: forall B C: ESet U, C <:= B \\// C.
Proof. firstorder. Qed.

Property intersect_inc: forall B C: ESet U, B //\\ C <:= B.
Proof. firstorder. Qed.
Property intersect_inc2: forall B C: ESet U, B //\\ C <:= C.
Proof. firstorder. Qed.

Property union_inc_split: forall A B C: ESet U, A \\// B <:= C <-> A <:= C /\ B <:= C.
Proof. firstorder. Qed.

Property intersect_inc_split: forall A B C: ESet U, C <:= A //\\ B <-> C <:= A /\ C <:= B.
Proof. firstorder. Qed.

Property inc_union_eq: forall B C: ESet U, B <:= C <-> B \\// C == C.
Proof. firstorder. Qed.

Property inc_intersect_eq: forall B C: ESet U, B <:= C <-> B //\\ C == B.
Proof. firstorder. Qed.

Lemma intersect_inc_distr: forall A B C D: ESet U,
  A <:= B -> C <:= D -> A //\\ C <:= B //\\ D.
Proof. firstorder. Qed.

Lemma union_inc_distr: forall A B C D: ESet U,
  A <:= B -> C <:= D -> A \\// C <:= B \\// D.
Proof. firstorder. Qed.

(* Interaction btwn union and intersection *)
Property union_intersect_distr: forall A B C: ESet U,
  C \\// (A //\\ B) == (C \\// A) //\\ (C \\// B).
Proof. firstorder. Qed.

Property intersect_union_distr: forall A B C: ESet U,
  C //\\ (A \\// B) == (C //\\ A) \\// (C //\\ B).
Proof. firstorder. Qed.


(* Complement properties *)

Lemma full_compl: ~! (@FullSet U) == (@EmptySet U).
Proof. firstorder. Qed.
Lemma empty_compl: ~! (@EmptySet U) == (@FullSet U).
Proof. firstorder. Qed.

Lemma union_compl: forall A B: ESet U, ~! (A \\// B) == (~! A) //\\ (~! B).
Proof. firstorder. Qed.

Lemma intersect_compl: forall A B: ESet U, ~! (A //\\ B) == (~! A) \\// (~! B).
Proof. split; firstorder.
  decides (x :in: A); firstorder. Qed.

Lemma compl_compl: forall A: ESet U, ~! (~! A) == A.
Proof. split; firstorder.
  decides (x :in: A); firstorder. Qed.

(* Setminus properties *)

Lemma setminus_as_intersect: forall B C: ESet U, B \\ C == B //\\ ~! C.
Proof. firstorder. Qed.

(* Singleton properties *)

Lemma singleton_def: forall U `(Setoid U) (x: U), x :in: {{ x }}.
Proof. move=> /=. reflexivity. Qed.

(* Inhabited properties *)
Lemma not_inhabited_empty: forall (A: ESet U),
  ~Inhabited A <-> A == EmptySet.
Proof. firstorder. Qed.


End SetOps.

#[export]
Hint Resolve
  inc_empty inc_full
  union_comm union_assoc intersect_comm intersect_assoc
  union_inc union_inc2 intersect_inc intersect_inc2
  union_inc_distr intersect_inc_distr
  union_intersect_distr intersect_union_distr
  full_compl empty_compl
  union_compl intersect_compl compl_compl
  setminus_as_intersect singleton_def: sets.
#[export]
Hint Resolve -> same_inc_iff
  union_inc_split intersect_inc_split
  inc_union_eq inc_intersect_eq: sets.
#[export]
Hint Resolve <- same_inc_iff
  union_iff intersect_iff compl_iff setminus_iff singleton_iff
  union_inc_split intersect_inc_split: sets.

(* ----------------------------------------------------------------- *)
(*                    Proper sets & Power Sets                       *)
(* ----------------------------------------------------------------- *)

(* Condition of Proper set *)
Class ProperSet {U} `{Setoid U} (P: ESet U): Prop :=
  set_proper: Morphisms.Proper (equiv ==> iff) (InSet P).

(* Membership of a proper set is a morphism on its element *)
Add Parametric Morphism U (P: ESet U) `{H: ProperSet _ P}: (InSet P)
  with signature equiv ==> iff as proper_in_mor.
Proof. apply: H. Qed.

Instance proper_singleton U `{Setoid U} (x: U):
  ProperSet {{ x }}.
Proof. move=> a b E. rewrite !singleton_iff. rw_refl. Qed. 

Instance proper_union U `{S: Setoid U} (A B: ESet U) `(@ProperSet _ S A) `(@ProperSet _ S B):
  @ProperSet _ S (A \\// B).
Proof. move=> a b E. rewrite !union_iff. rw_refl. Qed.

Instance proper_intersect U `{S: Setoid U} (A B: ESet U) `(@ProperSet _ S A) `(@ProperSet _ S B):
  @ProperSet _ S (A //\\ B).
Proof. move=> a b E. rewrite !intersect_iff. rw_refl. Qed.

Instance proper_compl U (A: ESet U) `(ProperSet _ A): ProperSet (~! A).
Proof. move=> a b E. rewrite !compl_iff. rw_refl. Qed.


(* Proper form of a given set *)
Definition properForm {U} `{Setoid U} (P: ESet U): ESet U :=
  mkSet (fun x => exists y, y :in: P /\ y == x).

Instance properform_proper U `{Setoid U} (P: ESet U): ProperSet (properForm P).
Proof. move=> a b E /=. split=> - [x [? F]]; exists x.
  all: by move: E F => ->. Qed.

Add Parametric Morphism U `(Setoid U): (@properForm U _)
  with signature equiv ==> equiv as proper_mor.
Proof. firstorder. Qed.


Definition Powerset (U:Type) := ESet (ESet U).

(* Power set included in certain set *)
Definition PsetOn {U} (A: ESet U): Powerset U := mkSet (fun V => V <:= A).

Property pseton_in_iff: forall U (A: ESet U) B,
  B :in: PsetOn A <-> B <:= A.
Proof. reflexivity. Qed.

Add Parametric Morphism U: (@PsetOn U)
  with signature equiv ==> equiv as pseton_mor.
Proof. firstorder. Qed.

#[export]
Hint Unfold properForm Powerset: sets.
#[export]
Hint Resolve -> pseton_in_iff: sets.


(* ----------------------------------------------------------------- *)
(*        Qualification over Powersets & Union over Powersets        *)
(* ----------------------------------------------------------------- *)

Definition ExistsIn {U} (A: ESet U) (P: U -> Prop): Prop :=
  exists x: U, x :in: A /\ P x.
Definition ForallIn {U} (A: ESet U) (P: U -> Prop): Prop :=
  forall x: U, x :in: A -> P x.

Definition Unions {U} (F: Powerset U): ESet U :=
  mkSet (fun x => ExistsIn F (fun A => x :in: A)).
Definition Intersects {U} (F: Powerset U): ESet U :=
  mkSet (fun x => ForallIn F (fun A => x :in: A)).

Add Parametric Morphism U: (@Unions U)
  with signature equiv ==> equiv as unions_mor.
Proof. firstorder. Qed.
Add Parametric Morphism U: (@Intersects U)
  with signature equiv ==> equiv as intersects_mor.
Proof. firstorder. Qed.


Property unions_iff: forall U x (F: Powerset U),
  x :in: Unions F <-> ExistsIn F (fun A => x :in: A).
Proof. firstorder. Qed.

Property intersects_iff: forall U x (F: Powerset U),
  x :in: Intersects F <-> ForallIn F (fun A => x :in: A).
Proof. firstorder. Qed.

(* Properties *)

Lemma unions_inc_one: forall U (A: ESet U) (F: Powerset U),
  A :in: F -> A <:= Unions F.
Proof. firstorder. Qed.

Lemma intersects_inced_one: forall U (A: ESet U) (F: Powerset U),
  A :in: F -> A =:> Intersects F.
Proof. firstorder. Qed.


Lemma unions_empty: forall U,
  Unions EmptySet == @EmptySet U.
Proof. firstorder. Qed.

Lemma intersects_empty: forall U,
  Intersects EmptySet == @FullSet U.
Proof. firstorder. Qed.

Lemma unions_single: forall U (A: ESet U),
  Unions ( {{ A }} ) == A.
Proof. firstorder. Qed.

Lemma intersects_single: forall U (A: ESet U),
  Intersects ( {{ A }} ) == A.
Proof. firstorder. Qed.

Lemma unions_couple: forall U (A B: ESet U),
  Unions ( {{ A, B }} ) == A \\// B.
Proof. firstorder. Qed.

Lemma intersects_couple: forall U (A B: ESet U),
  Intersects ( {{ A, B }} ) == A //\\ B.
Proof. firstorder. Qed.


Lemma inc_forall_unions_iff: forall U (A: ESet U) (F: Powerset U),
  (forall S, S :in: F -> A =:> S) <-> A =:> Unions F.
Proof. firstorder. Qed.

Lemma inced_forall_intersects_iff: forall U (A: ESet U) (F: Powerset U),
  (forall S, S :in: F -> A <:= S) <-> A <:= Intersects F.
Proof. firstorder. Qed.

Lemma inced_forall_then_inced_unions: forall U (A: ESet U) (F: Powerset U),
  Inhabited F -> (forall S, S :in: F -> A <:= S) -> A <:= Unions F.
Proof. firstorder. Qed.

Lemma inc_forall_then_inc_intersects: forall U (A: ESet U) (F: Powerset U),
  Inhabited F -> (forall S, S :in: F -> A =:> S) -> A =:> Intersects F.
Proof. firstorder. Qed.


#[export]
Hint Unfold ExistsIn ForallIn: sets.
#[export]
Hint Resolve
  unions_inc_one intersects_inced_one
  unions_empty intersects_empty unions_single intersects_single
  unions_couple intersects_couple: sets.
#[export]
Hint Resolve -> unions_iff intersects_iff: sets.
#[export]
Hint Resolve <- unions_iff intersects_iff: sets.


(* ----------------------------------------------------------------- *)
(*                     Image and InvImage(PreImage)                  *)
(* ----------------------------------------------------------------- *)

Section Mapping.
Context {U V:Type}.

Section DecMapping.
Context `{Setoid V}.

Definition Im (f: U -> V) (X: ESet U): ESet V :=
  mkSet (fun y => ExistsIn X (fun x => y == f x)).

(* For manual unfolding *)
Property im_iff: forall (X: ESet U) (f: U -> V) (y: V),
  y :in: Im f X <-> ExistsIn X (fun x => y == f x).
Proof. reflexivity. Qed.

Property im_def: forall (X: ESet U) (f: U -> V) (x: U),
  x :in: X -> f x :in: Im f X.
Proof. firstorder. Qed.


Lemma im_empty: forall (f: U -> V), Im f EmptySet == EmptySet.
Proof. firstorder. Qed.

Lemma im_intersect: forall (f: U -> V) (A B: ESet U),
  Im f (A //\\ B) <:= Im f A //\\ Im f B.
Proof. firstorder. Qed.

Lemma im_union: forall (f: U -> V) (A B: ESet U),
  Im f (A \\// B) == Im f A \\// Im f B.
Proof. firstorder. Qed.

Lemma im_inc: forall (f: U -> V) (A B: ESet U),
  A <:= B -> Im f A <:= Im f B.
Proof. firstorder. Qed.

End DecMapping.

Lemma forall_im_iff: forall `(UsualSetoid V) (A: ESet U) (f: U -> V) (P: V -> Prop),
  ForallIn (Im f A) P <-> ForallIn A (fun x => P (f x)).
Proof. rewrite /ForallIn /impl /=. firstorder; subst; auto. Qed.

Lemma exists_im_iff: forall `(UsualSetoid V) (A: ESet U) (f: U -> V) (P: V -> Prop),
  (exists y, y :in: Im f A /\ P y) <-> (exists x, x :in: A /\ P (f x)).
Proof. rewrite /ForallIn /impl /=. firstorder; subst; eauto. Qed.


Definition InvIm (f: U -> V) (Y: ESet V): ESet U :=
  mkSet (fun x => f x :in: Y).

(* For manual unfolding *)
Property invim_iff: forall (Y: ESet V) (f: U -> V) (x: U),
  x :in: InvIm f Y <-> (f x) :in: Y.
Proof. reflexivity. Qed.

Lemma invim_empty: forall (f: U -> V),
  InvIm f EmptySet == EmptySet.
Proof. firstorder. Qed.

Lemma invim_full: forall (f: U -> V),
  InvIm f FullSet == FullSet.
Proof. firstorder. Qed.

Lemma invim_intersect: forall (f: U -> V) (A B: ESet V),
  InvIm f (A //\\ B) == InvIm f A //\\ InvIm f B.
Proof. firstorder. Qed.

Lemma invim_union: forall (f: U -> V) (A B: ESet V),
  InvIm f (A \\// B) == InvIm f A \\// InvIm f B.
Proof. firstorder. Qed.

Lemma invim_inc: forall (f: U -> V) (A B: ESet V),
  A <:= B -> InvIm f A <:= InvIm f B.
Proof. firstorder. Qed.


Lemma invim_of_im_inc: forall `(Setoid V) (f: U -> V) (A: ESet U),
  InvIm f (Im f A) =:> A.
Proof. firstorder. Qed.

Lemma im_of_invim_inc: forall `(UsualSetoid V) (f: U -> V) (B: ESet V),
  Im f (InvIm f B) <:= B.
Proof. move=> * _ [x [? ->]]. auto. Qed.


Lemma invim_compl: forall (f: U -> V) (P: ESet V),
  ~! InvIm f P == InvIm f (~! P).
Proof. firstorder. Qed.

End Mapping.

Instance proper_im U V `{Setoid V} (X: ESet U) (f: U -> V): ProperSet (Im f X).
Proof. move=> y y' E. split=> - [x [? F]]; exists x. all: by move: E F => ->. Qed.


Add Parametric Morphism U V `(Setoid V): (@Im U V _)
  with signature equiv ==> equiv ==> equiv as im_mor.
Proof.
  move=> f g Hf A B HS. constructor=> s.
  split=> - [t [HI ->]]; exists t.
  all: move: HS HI => ->; auto.
Qed.

Add Parametric Morphism U V `(UsualSetoid V): (@InvIm U V)
  with signature equiv ==> equiv ==> equiv as invim_mor.
Proof. move=> f g Hf A B HS. constructor=> t /=.
  by move: (Hf t) HS => -> ->. Qed.

Add Parametric Morphism U V: (@InvIm U V)
  with signature eq ==> equiv ==> equiv as invim_eq_mor.
Proof. firstorder. Qed.


Lemma im_identity: forall U (A: ESet U) `(UsualSetoid U), Im id A == A.
Proof. move=> >. firstorder. by rewrite H0. Qed.

Lemma invim_identity: forall U (A: ESet U), InvIm id A == A.
Proof. firstorder. Qed.

Lemma im_compose: forall U V W `(DV: UsualSetoid V) `(DW: UsualSetoid W),
  forall (A: ESet U) (f: U -> V) (g: V -> W),
  Im (compose g f) A == Im g (Im f A).
Proof. move=> >. firstorder. rewrite H0 H1. firstorder. Qed.

Lemma invim_compose: forall U V W (C: ESet W) (f: U -> V) (g: V -> W),
  InvIm (compose g f) C == InvIm f (InvIm g C).
Proof. firstorder. Qed.


Lemma invim_of_im_eq_inj: forall U V `(D: UsualSetoid V) (f: U -> V) (A: ESet U),
  injective f -> InvIm f (Im f A) == A.
Proof.
  move=> > H. constructor=> x. rewrite invim_iff. split.
  - case=> x' [? +]. by move/H => ->.
  - apply: im_def.
Qed.

Lemma im_of_invim_eq_surj: forall U V `(D: UsualSetoid V) (f: U -> V) (B: ESet V),
  surjective f -> Im f (InvIm f B) == B.
Proof.
  move=> > H. constructor=> y. split.
  - by case=> x [? ->].
  - case: (H y) => [x ->] ?. by apply: im_def.
Qed.


(* Indexed, synonym for image, and its alternative notation *)
Definition Indexed {U V} `{Setoid V} (P: ESet U) (f: U -> V) :=
  Im f P.

Notation "'{''  E '|' x 'in' P  ''}'" :=
  (Indexed P (fun x => E))
  (at level 0, x binder, no associativity).


#[export]
Hint Transparent Indexed: sets.
#[export]
Hint Resolve im_def
  im_empty im_intersect im_union im_inc
  invim_empty invim_full invim_intersect invim_union invim_inc
  invim_of_im_inc im_of_invim_inc  invim_compl
  im_identity invim_identity: sets.
#[export]
Hint Resolve -> exists_im_iff forall_im_iff: sets.
#[export]
Hint Resolve <- im_iff invim_iff
  exists_im_iff forall_im_iff: sets.


(* ----------------------------------------------------------------- *)
(*                      UnionOver and IntersectOver                  *)
(* ----------------------------------------------------------------- *)

Definition UnionOver {U V} (P: ESet U) (f: U -> ESet V): ESet V :=
  Unions (Im f P).
Definition IntersectOver {U V} (P: ESet U) (f: U -> ESet V): ESet V :=
  Intersects (Im f P).

Notation "'unions' i 'in' P , e" := (UnionOver P (fun i => e))
  (at level 100, i binder, right associativity).
Notation "'intersects' i 'in' P , e" := (IntersectOver P (fun i => e))
  (at level 100, i binder, right associativity).

(* Not a simple restatement; does not involve equiv check here *)
Property unionover_iff: forall U V (P: ESet U) (E: U -> ESet V) y,
  y :in: (unions x in P, E x) <-> ExistsIn P (fun x => y :in: E x).
Proof. firstorder. Qed.

Property intersectover_iff: forall U V (P: ESet U) (E: U -> ESet V) y,
  y :in: (intersects x in P, E x) <-> ForallIn P (fun x => y :in: E x).
Proof. firstorder. Qed.

(* Purely for manual application *)
Property unionover_r: forall U V (P: ESet U) (E: U -> ESet V) y,
  y :in: (unions x in P, E x) -> ExistsIn P (fun x => y :in: E x).
  apply unionover_iff. Qed.
Property intersectover_r: forall U V (P: ESet U) (E: U -> ESet V) y,
  y :in: (intersects x in P, E x) -> ForallIn P (fun x => y :in: E x).
  apply intersectover_iff. Qed.

Add Parametric Morphism U V: (@UnionOver U V)
  with signature equiv ==> equiv ==> equiv as unionover_mor.
Proof.
  move=> *. constructor=> x.
  rewrite !unionover_iff. firstorder. Qed.

Add Parametric Morphism U V: (@IntersectOver U V)
  with signature equiv ==> equiv ==> equiv as intersectover_mor.
Proof.
  move=> *. constructor=> x.
  rewrite !intersectover_iff. firstorder. Qed.


Lemma unions_as_over: forall U (F: Powerset U),
  Unions F == (unions A in F, A).
Proof. firstorder. Qed.

Lemma intersects_as_over: forall U (F: Powerset U),
  Intersects F == (intersects A in F, A).
Proof. firstorder. Qed.


Lemma im_unionover: forall I U V `(Setoid V) (f: U -> V) (A: ESet I) (P: I -> ESet U),
  Im f (unions i in A, P i) == unions i in A, Im f (P i).
Proof.
  move=> *. constructor=> y.
  rewrite im_iff !unionover_iff. firstorder.
Qed.

Lemma im_intersectover: forall I U V `(Setoid V) (f: U -> V) (A: ESet I) (P: I -> ESet U),
  Im f (intersects i in A, P i) <:= intersects i in A, Im f (P i).
Proof.
  move=> * y. rewrite im_iff /ExistsIn.
  setoid_rewrite intersectover_iff. firstorder.
Qed.

Lemma invim_unionover: forall I U V (A: ESet I) (P: I -> ESet V) (f: U -> V),
  InvIm f (unions i in A, P i) == unions i in A, InvIm f (P i).
Proof.
  move=> *. constructor=> x.
  rewrite invim_iff !unionover_iff. firstorder.
Qed.

Lemma invim_intersectover: forall I U V (A: ESet I) (P: I -> ESet V) (f: U -> V),
  InvIm f (intersects i in A, P i) == intersects i in A, InvIm f (P i).
Proof.
  move=> *. constructor=> x.
  rewrite invim_iff !intersectover_iff. firstorder.
Qed.


Lemma unions_unionover: forall U I (A: ESet I) (F: I -> Powerset U),
  Unions (unions i in A, F i) == unions i in A, Unions (F i).
Proof.
  move=> *. constructor=> x. rewrite unions_iff /ExistsIn.
  setoid_rewrite unionover_iff. firstorder.
Qed.
(* NOTE: Any inclusion for intersects & intersectover does not hold *)

Lemma set_unionover: forall U `(UsualSetoid U) (A: ESet U),
  A == unions x in A, {{ x }}.
Proof.
  move=> *. constructor=> x. rewrite unionover_iff.
  firstorder. by move: H0 => <-. Qed.

Property unionover_inc_lift: forall (U:Type) (I:Type) (P: ESet I) (F G: I -> ESet U),
  ForallIn P (fun i => F i <:= G i) -> (unions i in P, F i) <:= (unions i in P, G i).
Proof.
  move=> * x. rewrite !unionover_iff. firstorder. Qed.

Property intersectover_inc_lift: forall (U:Type) (I:Type) (P: ESet I) (F G: I -> ESet U),
  ForallIn P (fun i => F i <:= G i) -> (intersects i in P, F i) <:= (intersects i in P, G i).
Proof. move=> * x. rewrite !intersectover_iff. firstorder. Qed.


Section OverOne.
Context (U:Type) (I:Type) (P: ESet I) (F: I -> ESet U).

Property unionover_inc_one: forall i: I,
  i :in: P -> F i <:= unions i in P, F i.
Proof. firstorder. Qed.

Property intersectover_inced_one: forall i: I,
  i :in: P -> F i =:> intersects i in P, F i.
Proof. firstorder. Qed.


Lemma inc_forall_unionover_iff: forall (A: ESet U),
  ForallIn P (fun i => A =:> F i) <-> A =:> unions i in P, F i.
Proof. unfold Include. setoid_rewrite unionover_iff. firstorder. Qed.

Lemma inced_forall_intersecover_iff: forall (A: ESet U),
  ForallIn P (fun i => A <:= F i) <-> A <:= intersects i in P, F i.
Proof. unfold Include. setoid_rewrite intersectover_iff. firstorder. Qed.

Lemma inced_forall_then_inced_unionover: forall (A: ESet U),
  Inhabited P -> ForallIn P (fun i => A <:= F i) -> A <:= unions i in P, F i.
Proof. move=> ? [? ?] ?. apply: inced_forall_then_inced_unions; firstorder. Qed.

Lemma inc_forall_then_inc_intersectover: forall (A: ESet U),
  Inhabited P -> ForallIn P (fun i => A =:> F i) -> A =:> intersects i in P, F i.
Proof. move=> ? [? ?] ?. apply: inc_forall_then_inc_intersects; firstorder. Qed.


Lemma unionover_compl:
  ~! (unions i in P, F i) == intersects i in P, (~! F i).
Proof. constructor=> x.
  rewrite compl_iff intersectover_iff unionover_iff. firstorder. Qed.

Lemma intersectover_compl:
  ~! (intersects i in P, F i) == unions i in P, (~! F i).
Proof. constructor=> x.
  rewrite compl_iff intersectover_iff unionover_iff. firstorder.
  contra. apply: H => i Hi. contra. firstorder.
Qed.

End OverOne.


Local Lemma unions_exch_: forall U I J (A: ESet I) (B: ESet J) (P: I -> J -> ESet U),
  (unions i in A, unions j in B, P i j) <:=
  (unions j in B, unions i in A, P i j).
Proof. move=> >. rewrite !unionover_iff. firstorder. Qed.

Lemma unions_exch: forall U I J (A: ESet I) (B: ESet J) (P: I -> J -> ESet U),
  (unions i in A, unions j in B, P i j) ==
  (unions j in B, unions i in A, P i j).
Proof. constructor; split; apply unions_exch_. Qed.

Local Lemma intersects_exch_: forall U I J (A: ESet I) (B: ESet J) (P: I -> J -> ESet U),
  (intersects i in A, intersects j in B, P i j) <:=
  (intersects j in B, intersects i in A, P i j).
Proof. move=> >. rewrite !intersectover_iff. firstorder. Qed.
Lemma intersects_exch: forall U I J (A: ESet I) (B: ESet J)
  (P: I -> J -> ESet U),
  (intersects i in A, intersects j in B, P i j) ==
  (intersects j in B, intersects i in A, P i j).
Proof. constructor; split; apply intersects_exch_. Qed.


(* Obvious distribution lemmas *)
Lemma intersect_distr_intersects: forall U I (A: ESet U) (K: ESet I) (P: I -> ESet U),
  Inhabited K -> A //\\ (intersects i in K, P i) == (intersects i in K, (A //\\ P i)).
Proof. move=> > [y ?]. constructor=> x.
  rewrite intersect_iff !intersectover_iff. firstorder. Qed.

Lemma union_distr_unions: forall U I (A: ESet U) (K: ESet I) (P: I -> ESet U),
  Inhabited K -> A \\// (unions i in K, P i) == (unions i in K, A \\// P i).
Proof. move=> > [y ?]. constructor=> x.
  rewrite union_iff !unionover_iff. firstorder. Qed.


(* Less obvious distribution lemmas *)
Lemma intersect_distr_unions: forall U I (A: ESet U) (K: ESet I) (P: I -> ESet U),
  A //\\ (unions i in K, P i) == (unions i in K, (A //\\ P i)).
Proof. move=> >. constructor=> x.
  rewrite intersect_iff !unionover_iff. firstorder. Qed.

(* Requires LEM *)
Lemma union_distr_intersects: forall U I (A: ESet U) (K: ESet I) (P: I -> ESet U),
  A \\// (intersects i in K, P i) == intersects i in K, (A \\// P i).
Proof. move=> ? ? A >. constructor=> x.
  rewrite union_iff !intersectover_iff.
  decides (x :in: A); firstorder.
Qed.


(* #[export]
Hint Unfold UnionOver IntersectOver: sets. *)
#[export]
Hint Resolve
  im_unionover im_intersectover invim_unionover invim_intersectover
  unions_unionover unionover_inc_lift intersectover_inc_lift
  unionover_inc_one intersectover_inced_one
  inced_forall_then_inced_unionover inc_forall_then_inc_intersectover
  unionover_compl intersectover_compl
  unions_exch intersects_exch: sets.
#[export]
Hint Resolve -> unionover_iff intersectover_iff
  inc_forall_unionover_iff inced_forall_intersecover_iff: sets.
#[export]
Hint Resolve <- unionover_iff intersectover_iff
  inc_forall_unionover_iff inced_forall_intersecover_iff: sets.


(* ----------------------------------------------------------------- *)
(*                              Subsets                              *)
(* ----------------------------------------------------------------- *)

Definition Subset {U} (A: ESet U): Type := { x: U | x :in: A }.

(* Inclusion *)
Definition inclu {U} {A: ESet U}: Subset A -> U := get.

Lemma subs_eq: forall U (A: ESet U) (x y: Subset A),
  inclu x = inclu y <-> x = y.
Proof. move=> >. symmetry. apply: sig_eq_iff. Qed.


Section Subset.
Context {U:Type} `(UsualSetoid U) {A: ESet U}.

Lemma incl_im_of_invim: forall B, Im (@inclu _ A) (InvIm inclu B) == A //\\ B.
Proof.
  move=> >. constructor=> x. rewrite im_iff intersect_iff. split.
  - by move=> [[? ?] [? ->]].
  - move=> [HxA ?]. by exists (exist _ x HxA).
Qed.

Lemma incl_invim_of_im: forall C, InvIm (@inclu _ A) (Im inclu C) == C.
Proof.
  move=> >. constructor=> x. split; [| firstorder].
  by case/invim_iff => [x' [? /subs_eq ->]].
Qed.

End Subset.

#[export]
Hint Unfold Subset inclu: sets.
#[export]
Hint Resolve incl_im_of_invim incl_invim_of_im: sets.
#[export]
Hint Resolve -> subs_eq: sets.
#[export]
Hint Resolve <- subs_eq: sets.


(* Notation for set restricted via condition *)
Notation "'{:'  x 'in' A '|' P  ':}'" :=
  ( A //\\ mkSet (fun x => P) )
  (at level 0, x binder, no associativity).

(* ----------------------------------------------------------------- *)
(*                             Products                              *)
(* ----------------------------------------------------------------- *)

Section AProd.
Context {U:Type} {V:Type}.

Definition Product (A: ESet U) (B: ESet V): ESet (U * V) :=
  mkSet (fun '(x, y) => x :in: A /\ y :in: B).

(* For rewrite / application *)
Property prod_iff: forall x y A B, (x, y) :in: Product A B <-> x :in: A /\ y :in: B.
Proof. firstorder. Qed.

Property prod_r: forall x y A B, (x, y) :in: Product A B -> x :in: A /\ y :in: B.
Proof. apply prod_iff. Qed.

(* Interaction with Fst / Snd *)
Property prod_fst_in: forall p A B, p :in: Product A B -> fst p :in: A.
Proof. case=> []. firstorder. Qed.

Property prod_snd_in: forall p A B, p :in: Product A B -> snd p :in: B.
Proof. case=> []. firstorder. Qed.

End AProd.

Notation "A '**' B" := (Product A B) (at level 40, left associativity).

Add Parametric Morphism U V: (@Product U V)
  with signature equiv ==> equiv ==> equiv as prod_mor.
Proof. move=> *. constructor=> - []. firstorder. Qed.


Section AProd.
Context {U V:Type}.

Lemma empty_l_prod: forall B, EmptySet ** B == @EmptySet (U * V).
Proof. move=> ?. constructor=> - []. firstorder. Qed.
Lemma empty_r_prod: forall A, A ** EmptySet == @EmptySet (U * V).
Proof. move=> ?. constructor=> - []. firstorder. Qed.

Lemma full_prod: FullSet ** FullSet == @FullSet (U * V).
Proof. constructor=> - []. firstorder. Qed.


Lemma prod_comm_in: forall (A: ESet U) (B: ESet V) x y,
  (x, y) :in: A ** B <-> (y, x) :in: B ** A.
Proof. firstorder. Qed.

Lemma prod_assoc_in: forall W (A: ESet U) (B: ESet V) (C: ESet W) x y z,
  (x, (y, z)) :in: A ** (B ** C) <-> (x, y, z) :in: A ** B ** C.
Proof. firstorder. Qed.


Lemma prod_inc_distr: forall (A C: ESet U) (B D: ESet V),
  A <:= C -> B <:= D -> A ** B <:= C ** D.
Proof. move=> * []. firstorder. Qed.


Lemma im_fst_prod: forall (A: ESet U) (B: ESet V) `(UsualSetoid U),
  Inhabited B -> Im fst (A ** B) == A.
Proof. move=> > [y ?]. constructor=> x. split.
  - case=> [? [+ ->]]. apply: prod_fst_in.
  - by exists (x, y).
Qed.

Lemma im_snd_prod: forall (A: ESet U) (B: ESet V) `(UsualSetoid V),
  Inhabited A -> Im snd (A ** B) == B.
Proof. move=> > [x ?]. constructor=> y. split.
  - case=> [? [+ ->]]. apply: prod_snd_in.
  - by exists (x, y).
Qed.

Lemma invim_fst_prod: forall (A: ESet U), InvIm fst A == A ** @FullSet V.
Proof. move=> ?. constructor=> - []. firstorder. Qed.

Lemma invim_snd_prod: forall (B: ESet V), InvIm snd B == @FullSet U ** B.
Proof. move=> ?. constructor=> - []. firstorder. Qed.

Lemma prod_invim_split: forall (A: ESet U) (B: ESet V),
  InvIm fst A //\\ InvIm snd B == A ** B.
Proof. move=> >. constructor=> - []. firstorder. Qed.

Lemma prod_intersect_exch: forall (A C: ESet U) (B D: ESet V),
  (A ** B) //\\ (C ** D) == (A //\\ C) ** (B //\\ D).
Proof. move=> *. constructor=> - []. firstorder. Qed.


Lemma indexed_prod_comm: forall S `(Setoid S) (P: ESet U) (Q: ESet V) (f: U -> V -> S),
  {' f x y | '(x, y) in P ** Q '} == {' f x y | '(y, x) in Q ** P '}.
Proof.
  move=> >. constructor=> t.
  split=> - [[u v] [? ->]].
  all: exists (v, u); firstorder.
Qed.

Lemma indexed_prod_assoc: forall W S `(Setoid S)
  (P: ESet U) (Q: ESet V) (R: ESet W) (f: U -> V -> W -> S),
  {' f x y z | '(x, (y, z)) in P ** (Q ** R) '} ==
  {' f x y z | '(x, y, z) in P ** Q ** R '}.
Proof.
  move=> >. constructor=> t.
  split=> [[[u [v w]] ] | [[[u v] w]] ] [? ->].
  all: exists ((u, v), w) || exists (u, (v, w)); firstorder.
Qed.


(* Subset and Product *)
Program Definition ps_to_sp {A: ESet U} {B: ESet V}:
  Subset A * Subset B -> Subset (A ** B) :=
  fun p => exist _ (inclu (fst p), inclu (snd p)) _.
Next Obligation. split; apply: getPr. Qed.

Program Definition sp_to_ps {A: ESet U} {B: ESet V}:
  Subset (A ** B) -> Subset A * Subset B :=
  fun p => (exist _ (fst (inclu p)) _, exist _ (snd (inclu p)) _).
Next Obligation. apply: prod_fst_in. apply: getPr. Qed.
Next Obligation. apply: prod_snd_in. apply: getPr. Qed.

Property prod_sub_id: forall A B (p: Subset A * Subset B),
  sp_to_ps (ps_to_sp p) = p.
Proof. move=> A B p. apply: injective_projections.
  all: by rewrite <- subs_eq. Qed.

Property sub_prod_id: forall A B (t: Subset (A ** B)),
  (ps_to_sp (sp_to_ps t)) = t.
Proof. move=> A B t. rewrite <- subs_eq.
  symmetry. by apply surjective_pairing. Qed.

End AProd.

#[export]
Hint Unfold ps_to_sp sp_to_ps: sets.
#[export]
Hint Resolve prod_fst_in prod_snd_in
  empty_l_prod empty_r_prod full_prod
  prod_comm_in prod_assoc_in  prod_inc_distr
  im_fst_prod im_snd_prod invim_fst_prod invim_snd_prod
  prod_invim_split prod_intersect_exch
  indexed_prod_comm indexed_prod_assoc: sets.
#[export]
Hint Resolve <- prod_iff: sets.
