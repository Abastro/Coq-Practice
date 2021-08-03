Require Import Basics.
Require Import Setoid.
Require Import RelationClasses.

Require Import Ensembles.
Require Import Constructive_sets.

Require Import Fin.
Require List.

From Practice Require Import Base.
From Practice Require Import Sets.
From Practice Require Import Image.
From Practice Require Import Product.

Definition Fin := Fin.t.

Module ToposSet.
Import Base.
Import Set_Extras.
Import Images.
Import Products.

Record isTopology {X:Type} (open: Ensemble X -> Prop): Prop := {
  open_empty_total: open (Empty_set _) /\ open (Full_set _)
; open_union: forall (M: PowerEn X), ForallIn M open -> open (Unions M)
; open_intersect: forall U V: Ensemble X, open U -> open V -> open (U //\\ V)
}.
Definition Topology (X:Type) := { op: Powerset X | isTopology (get op) }.
Arguments open_empty_total {X} {open}.
Arguments open_union {X} {open}.
Arguments open_intersect {X} {open}.

Definition open {X:Type} (T: Topology X): Ensemble X -> Prop := get (get T).
(* Closed <-> complement is open *)
Definition closed {X:Type} (T: Topology X): Ensemble X -> Prop :=
  fun E => open(T) (~! E).

Definition covers {X:Type} (V: Ensemble X) (C: PowerEn X): Prop :=
  V <:= Unions C.
Notation cover_all := (covers (Full_set _)).

Definition makeTopo {X:Type} (C: PowerEn X): properPset C -> isTopology C -> Topology X :=
  fun HP HB => exist _ (exist _ _ HP) HB.
Property makeTopo_spec: forall X (C: PowerEn X) HP HB, open (makeTopo C HP HB) = C.
Proof. auto. Qed.


(* ----------------------------------------------------------------- *)
(*                         Topology Basis                            *)
(* ----------------------------------------------------------------- *)

Definition gopen {X:Type} {P: Powerset X -> Prop} (G: sig P): Ensemble X -> Prop := get (get G).

Record isBase {X:Type} (open: Ensemble X -> Prop) : Type := {
  bopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
; bopen_intersect: forall (U V: Ensemble X) x,
  open U -> open V -> x :in: U //\\ V -> exists W, open W /\ x :in: W /\ (W <:= U //\\ V)
}.
Definition Basis (X:Type) := { op: Powerset X | isBase (get op) }.
Arguments bopen_cover {X} {open}.
Arguments bopen_intersect {X} {open}.

Record isSubbase {X:Type} (open: Ensemble X -> Prop) : Type := {
  sopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
}.
Definition Subbasis (X:Type) := { op: Powerset X | isSubbase (get op) }.
Arguments sopen_cover {X} {open}.

Section Base.
Context {X:Type}.

(* Basis/Subbasis construction *)
Definition makeBasis (C: PowerEn X): properPset C -> isBase C -> Basis X :=
  fun HP HB => exist _ (exist _ _ HP) HB.
Property makeBasis_spec: forall (C: PowerEn X) HP HB, gopen (makeBasis C HP HB) = C.
Proof. auto. Qed.
Property makeBasis_ (C: PowerEn X):
  properPset C -> isBase C -> exists B: Basis X, gopen B = C.
Proof. intros HP HB. exists (makeBasis _ HP HB). auto. Qed.

Definition makeSubbasis (C: PowerEn X): properPset C -> isSubbase C -> Subbasis X :=
  fun HP HB => exist _ (exist _ _ HP) HB.
Property makeSubbasis_spec: forall (C: PowerEn X) HP HB, gopen (makeSubbasis C HP HB) = C.
Proof. auto. Qed.
Property makeSubbasis_ (C: PowerEn X):
  properPset C -> isSubbase C -> exists S: Subbasis X, gopen S = C.
Proof. intros HP HB. exists (makeSubbasis _ HP HB). auto. Qed.


(* Obvious lemmas *)
Property topology_is_base (T: Topology X): isBase (open(T)).
Proof with (auto with sets). split.
  - exists ( {|' Full_set X '|} ).
    split. intros S []. apply (open_empty_total(getPr T)). red...
  - intros. exists (U //\\ V). split... apply (open_intersect(getPr T))...
Qed.

Property base_is_subbase (B: Basis X): isSubbase (gopen(B)).
Proof with (auto with sets). split. apply (bopen_cover(getPr B)). Qed.

(* Generation *)
Definition refiner (U: Ensemble X) (x: X): PowerEn X :=
  fun S => x :in: S /\ S <:= U.

Definition topoFromBase (B: PowerEn X): PowerEn X :=
  fun U => forall x, x :in: U -> ExistsIn B (refiner U x).
Property topoFromBase_proper (B: PowerEn X): properPset (topoFromBase B).
Proof. do 3 red. unfold topoFromBase, refiner, ExistsIn. intros. rw_refl. Qed.

Lemma base_is_open: forall B, B <:= topoFromBase B.
Proof. intros ? S ? ? ?. exists S. unfold refiner. auto with sets. Qed.

Property generate_by_base (B: Basis X): isTopology (topoFromBase (gopen B)).
Proof with (eauto with sets). split; unfold topoFromBase.
- (* Empty & Full *)
  split; try contradiction.
  destruct (bopen_cover(getPr B)) as [C [? HC]].
  intros ? [U []]%HC %unions_iff. exists U. unfold refiner. split... apply H...
- (* Unions *)
  intros ? H ? [U [I0 I1]]%unions_iff. apply H in I1 as HE... clear H.
  destruct HE as [S (? & ? & ?)]. exists S. repeat split...
- (* Intersection *)
  intros ? ? HU HV ? [IU IV]%intersection_iff.
  specialize (HU _ IU) as [S (HU1 & HU2 & HU3)]. specialize (HV _ IV) as [T (HV1 & HV2 & HV3)].
  destruct (bopen_intersect(getPr B) _ _ x HU1 HV1) as [W (H1 & H2 & H3)]...
  exists W. split... split; auto. etransitivity...
Qed.

Lemma open_iff_base_unions: forall (B: Basis X),
  topoFromBase (gopen B) '= indexed F in PSeton (gopen B), Unions F.
Proof with (eauto with sets).
  intros. intros U. rewrite indexed_iff. split.
  - (* <:= *)
    intros H.
    exists (unions x in U, fun S => S :in: gopen(B) /\ refiner U x S). split.
    + do 2 red. apply inc_forall_unionover_iff. firstorder.
    + apply same_set_eq. split.
      * apply inc_forall_unions_iff. intros S [x [? [? ?]]]%unionover_iff. firstorder.
      * intros x Hx. rewrite unions_unionover. apply unionover_iff. exists x. split...
        apply unions_iff. apply H in Hx as [S ?]. exists S. split...
        unfold refiner in *. tauto.
  - (* =:> *)
    intros [F (? & E%symmetry)].
    eapply topoFromBase_proper... simpl. do 2 red in H.
    apply (open_union (generate_by_base B)). intros ? ?. apply base_is_open...
Qed.


Definition baseFromSubbase (S: PowerEn X): PowerEn X :=
  fun V => exists (L: list (Ensemble X)), List.Forall S L /\ V '= IntersectList L.

Property baseFromSubbase_proper (S: PowerEn X): properPset (baseFromSubbase S).
Proof. do 3 red. intros. unfold baseFromSubbase. rw_refl. Qed.

Property generate_by_subbase (S: Subbasis X): isBase (baseFromSubbase (gopen S)).
Proof with (auto with sets).
  split.
  - (* Covers *)
    destruct (sopen_cover(getPr S)) as [C []]. exists C. split... unfold ForallIn.
    intros U A. exists (cons U nil). unfold gopen.
    split... unfold IntersectList...
  - (* Intersects *)
    intros ? ? ? [LU (AU & EU)] [LV (AV & EV)] HI. exists (U //\\ V).
    split... unfold baseFromSubbase.
    exists (app LU LV). split; [ apply List.Forall_app | ]...
    rewrite EU, EV. clear AU AV EU EV.
    induction LU; unfold app, IntersectList;
    [ rewrite intersection_comm | rewrite <- IHLU ]...
Qed.

Program Definition topoByBase (B: Basis X): Topology X := makeTopo (topoFromBase (gopen B)) _ _.
Next Obligation. apply topoFromBase_proper. Qed.
Next Obligation. apply generate_by_base. Qed.

Program Definition baseBySubbase (S: Subbasis X): Basis X := makeBasis (baseFromSubbase (gopen S)) _ _.
Next Obligation. apply baseFromSubbase_proper. Qed.
Next Obligation. apply generate_by_subbase. Qed.

(*  Denotes is that certain powerset serves as a base of the topology *)
Definition isBaseOf (C: PowerEn X) (T: Topology X): Prop :=
  exists B: Basis X, gopen (B) = C /\ topoByBase B '= T.
Definition isSubbaseOf (C: PowerEn X) (T: Topology X): Prop :=
  exists S: Subbasis X, gopen(S) = C /\ topoByBase (baseBySubbase S) '= T.

(* Topology generated by Basis / Subbasis is minimal -> so it is unique *)
Lemma basis_gen_minimal: forall (B: Basis X) (T: Topology X),
  gopen(B) <:= open(T) -> open(topoByBase B) <:= open(T).
Proof.
  intros ? ? H. unfold topoByBase, open. simpl.
  rewrite open_iff_base_unions. intros U [F (? & ?%symmetry)]%indexed_r.
  pose proof (K := getPr (get T)); simpl in K. eapply K; eauto.
  apply (open_union (getPr T)). firstorder.
Qed.

Lemma subbasis_gen_minimal: forall (S: Subbasis X) (T: Topology X),
  gopen(S) <:= open(T) -> gopen (topoByBase (baseBySubbase S)) <:= open(T).
Proof.
  intros ? ? H. apply basis_gen_minimal.
  unfold baseBySubbase, gopen. simpl. intros F [G (H1 & H2)].
  pose proof (K := getPr (get T)); simpl in K. eapply K; eauto. clear H2 K.
  induction G as [| W G]; simpl.
  - apply (open_empty_total(getPr T)).
  - inversion H1; subst. apply (open_intersect (getPr T)); auto. firstorder.
Qed.


Lemma identify_base: forall (T: Topology X) (C: PowerEn X),
  properPset C -> C <:= open(T) ->
  ForallIn (open T) (fun U => forall x, x :in: U -> ExistsIn C (refiner U x)) ->
  isBaseOf C T.
Proof with (eauto with sets).
  intros ? ? HP HI H. destruct (makeBasis_ C) as [B ?].
  - apply HP.
  - (* Is Basis *) split.
    + (* Cover *)
      exists C. split... unfold cover_all.
      intros x [V (? & ? & ?)]%H... apply (open_empty_total(getPr T)).
    + (* Intersection *)
      intros * HU%HI HV%HI IN.
      specialize (open_intersect(getPr T) _ _ HU HV) as HN %H.
      specialize (HN x IN) as [W ?]...
  - (* Generates *)
    exists B. split; [auto|]; subst. apply same_set_eq. simpl. split.
    + (* open T =:> *) apply basis_gen_minimal...
    + (* open T <:= *) intros U HU%H...
Qed.

End Base.


(* ----------------------------------------------------------------- *)
(*                       Subspace Topology                           *)
(* ----------------------------------------------------------------- *)

(* Subspace topology *)
Section Subspace.
Context {X:Type}.
Context (T: Topology X) (A: Ensemble X).

Definition subsetOver: PowerEn X -> PowerEn (Subset A) :=
  fun C => indexed U in C, InvIm U incl.

Property subspOpen_proper: properPset (subsetOver (open T)).
Proof. apply properForm_spec. Qed.

Property subspace_topo: isTopology (subsetOver (open T)).
Proof with (eauto with sets).
  split; unfold subsetOver.
  - (* empty & full *)
    split; apply indexed_iff.
    + exists (Empty_set _). split... apply (open_empty_total (getPr T)).
    + exists (Full_set _). split... apply (open_empty_total (getPr T)).

  - (* unions *)
    intros. apply indexed_iff.
    exists (Unions (fun U => U :in: open(T) /\ InvIm U incl :in: properForm M)). split.
    + apply (open_union (getPr T)). intros ? []...
    + rewrite <- unions_as_over. rewrite invim_unionover.
      apply same_set_eq. split.
      * apply inc_forall_unionover_iff. intros U [? [V [? <-]]]...
      * apply inc_forall_unions_iff. intros V HV.
        specialize (H _ HV) as [U [H1 H2]]%indexed_r. rewrite <- H2.
        apply unionover_inc_one with (F := fun T => InvIm T incl).
        split... rewrite H2...

  - (* intersection *)
    intros U U' [V [HV1 HV2]]%indexed_r [V' [HV'1 HV'2]]%indexed_r.
    apply indexed_iff. exists (V //\\ V'). rewrite invim_intersect.
    split; [apply (open_intersect (getPr T)) | all_rewrite ]...
Qed.

Program Definition SubspaceT: Topology (Subset A) := makeTopo (subsetOver (open T)) _ _.
Next Obligation. apply subspOpen_proper. Qed.
Next Obligation. apply subspace_topo. Qed.


Lemma subsp_basis_from_basis: forall C: PowerEn X,
  isBaseOf C T -> isBaseOf (subsetOver C) SubspaceT.
Proof with (auto with sets).
  intros ? [B (<- & HE)]. do 4 red in HE. apply identify_base.
  - (* Proper *) apply properForm_spec.

  - (* Containment *)
    intros U [V []]%indexed_r. apply indexed_iff.
    exists V. split... setoid_rewrite <- HE. apply base_is_open...

  - (* Forms basis *)
    intros V [U (H1 & H2)]%indexed_r y Hy. rewrite <- H2 in Hy.
    apply invim_iff in Hy. setoid_rewrite <- HE in H1. unfold subsetOver.
    specialize (H1 (incl y) Hy) as [W (? & ? & ?)].
    exists (InvIm W incl). split; eauto with sets. split; try rewrite <- H2...
Qed.


Lemma open_subsp_open_whole: forall U: Ensemble (Subset A),
  open(T) A -> open(SubspaceT) U -> open(T) (Im U incl).
Proof with (eauto with sets).
  intros. do 8 red in H0. apply indexed_r in H0 as [V []].
  assert (Im U incl '= A //\\ V); [rewrite <- H1|]...
  eapply (getPr (get T))... apply (open_intersect (getPr T))...
Qed.

End Subspace.

(* ----------------------------------------------------------------- *)
(*                        Product Topology                           *)
(* ----------------------------------------------------------------- *)

Section Product.
Context {X:Type} {Y:Type}.
Context (S: Topology X) (T: Topology Y).

Definition prodOver: PowerEn X -> PowerEn Y -> PowerEn (X * Y) :=
  fun C D => indexed P in C ** D, fst P ** snd P.

Property prod_basis: isBase (prodOver (open S) (open T)).
Proof with (eauto with sets).
  split; unfold prodOver.
  - (* Covers *)
    exists ( {|' Full_set (X * Y) '|} ). split.
    + intros ? []. apply indexed_iff. eexists. split. split.
      apply (open_empty_total(getPr S)). apply (open_empty_total(getPr T)). auto...
    + red...

  - (* Intersection *)
    intros T1 T2 x [(U1, V1) [H1 E1]]%indexed_r [(U2, V2) [H2 E2]]%indexed_r H.
    exists (T1 //\\ T2). split; [| all_rewrite]...
    apply prod_iff in H1 as (HU1 & HV1). apply prod_iff in H2 as (HU2 & HV2).
    pose proof (H1 := open_intersect (getPr S) _ _ HU1 HU2).
    pose proof (H2 := open_intersect (getPr T) _ _ HV1 HV2).
    apply indexed_iff. eexists. split. split... rewrite <- E1, <- E2...
Qed.

Program Definition ProductB: Basis (X * Y) := makeBasis (prodOver (open S) (open T)) _ _.
Next Obligation. apply properForm_spec. Qed.
Next Obligation. apply prod_basis. Qed.

Definition ProductT: Topology (X * Y) := topoByBase ProductB.

Lemma prod_basis_from_basis: forall (B: PowerEn X) (C: PowerEn Y),
  isBaseOf B S -> isBaseOf C T ->
  isBaseOf (prodOver B C) ProductT.
Proof with (eauto with sets).
  intros * [Bt (? & EB)] [Ct (? & EC)]; subst. apply identify_base.
  - apply properForm_spec.

  - (* Contained in ProductT *)
    etransitivity; [| apply base_is_open]. unfold ProductB. rewrite makeBasis_spec.
    intros P [(U, V) (? & ?)]%indexed_r. apply indexed_iff. exists (U, V).
    split... rewrite prod_iff in *. firstorder.

  - (* Defining condition for the basis *)
    intros W HW (x, y) Hxy.
    specialize (HW (x, y) Hxy) as [P [[(U, V) (HI & HE)]%indexed_r [HR1 HR2]]].
    unfold fst, snd in HE. rewrite <- HE in *.
    apply prod_iff in HI as [HU%EB HV%EC]. apply prod_iff in HR1 as (HU2 & HV2).
    specialize (HU x HU2) as [I (HI1 & HI2)]. specialize (HV y HV2) as [J (HJ1 & HJ2)].
    exists (I ** J). split. apply indexed_iff...
    unfold refiner in *. destruct HI2, HJ2. split; [eauto with sets|].
    etransitivity; eauto...
Qed.


Definition prodSubbasis: PowerEn (X * Y) :=
  (indexed U in open S, InvIm U fst) \\// (indexed V in open T, InvIm V snd).

Theorem prod_subbasis_spec:
  isSubbaseOf prodSubbasis ProductT.
Proof with (eauto with sets).
  destruct (makeSubbasis_ prodSubbasis) as [B HS].
  - (* Proper *)
    do 3 red. intros. unfold prodSubbasis. setoid_rewrite union_iff. rw_refl.

  - (* Subbase (cover) *)
    split. exists ( {|' Full_set (X * Y) '|} ). split; [| unfold cover_all]...
    intros ? []. left. apply indexed_iff. eexists. split... apply (open_empty_total(getPr S)).

  - (* Generates exact *)
    exists B. split; auto. apply same_set_eq. split.
    + (* open ProductT =:> *)  (* This is too meh *)
      apply subbasis_gen_minimal. unfold ProductT, topoByBase. rewrite makeTopo_spec.
      etransitivity; [| apply base_is_open]. rewrite HS. unfold prodSubbasis.
      apply union_incl_split. split; intros P [U (? & HE)]%indexed_r;
        [rewrite invim_fst_prod in HE | rewrite invim_snd_prod in HE].
      all: apply indexed_iff; eexists (_, _).
      all: unfold fst, snd.  all: split; eauto.  all: apply prod_iff; split...
      apply (open_empty_total(getPr T)). apply (open_empty_total (getPr S)).
    + (* open ProductT <:= *)
      unfold ProductT. apply basis_gen_minimal. etransitivity; [| apply base_is_open].
      intros P [(U, V) [[HU HV]%prod_iff HP]]%indexed_r.
      exists (cons (InvIm U fst) (cons (InvIm V snd) nil)). rewrite HS. split.
      * repeat apply List.Forall_cons; [left | right | constructor]...
      * unfold IntersectList. rewrite <- intersection_assoc, prod_invim_split...
Qed.

End Product.

End ToposSet.

