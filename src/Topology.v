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

Notation Conded X F := { op: PowerEn X | properPset op /\ F op }.

Section Conded.
Context {X:Type} {F: PowerEn X -> Prop}.

Definition makeCond (C: PowerEn X): properPset C /\ F C -> Conded X F :=
  fun H => exist _ _ H.
Property makeCond_spec: forall C H, get (makeCond C H) = C.
Proof. auto. Qed.

Definition properPf {X:Type} {F: PowerEn X -> Prop}
  (T: Conded X F): properPset (get T) := proj1 (getPr T).
Definition condPf {X:Type} {F: PowerEn X -> Prop}
  (T: Conded X F): F (get T) := proj2 (getPr T).

End Conded.

Property makeCond_pf {X:Type}: forall (F: PowerEn X -> Prop) C,
  properPset C -> F C -> exists S: Conded X F, get S = C.
Proof. intros * HP HB. exists (makeCond _ (conj HP HB)). auto. Qed.

Record isTopology {X:Type} (open: Ensemble X -> Prop): Prop := {
  open_empty_total: open (Empty_set _) /\ open (Full_set _)
; open_union: forall (M: PowerEn X), ForallIn M open -> open (Unions M)
; open_intersect: forall U V: Ensemble X, open U -> open V -> open (U //\\ V)
}.
Definition Topology (X:Type) := Conded X isTopology.
Arguments open_empty_total {X} {open}.
Arguments open_union {X} {open}.
Arguments open_intersect {X} {open}.

Definition open {X:Type} {F: PowerEn X -> Prop} (T: Conded X F): PowerEn X := get T.
(* Closed <-> complement is open *)
Definition closed {X:Type} {F: PowerEn X -> Prop} (T: Conded X F): PowerEn X :=
  fun E => open(T) (~! E).

Definition covers {X:Type} (V: Ensemble X) (C: PowerEn X): Prop :=
  V <:= Unions C.
Notation cover_all := (covers (Full_set _)).

(* ----------------------------------------------------------------- *)
(*                       General Properties                          *)
(* ----------------------------------------------------------------- *)

Section Topo.
Context {X:Type} (T: Topology X).

(* Restatements *)
Property empty_open: open(T) (Empty_set _).
Proof. apply (open_empty_total (condPf T)). Qed.

Property full_open: open(T) (Full_set _).
Proof. apply (open_empty_total (condPf T)). Qed.

Property unions_open: forall M: PowerEn X, ForallIn M (open(T)) -> open(T) (Unions M).
Proof. apply (open_union (condPf T)). Qed.

Property intersect_open: forall U V: Ensemble X, open(T) U -> open(T) V -> open(T) (U //\\ V).
Proof. apply (open_intersect (condPf T)). Qed.

Lemma union_open: forall U V: Ensemble X, open(T) U -> open(T) V -> open(T) (U \\// V).
Proof with auto. intros.
  eapply properPf. symmetry. apply unions_couple.
  apply unions_open. intros ? [? []| ? []]...
Qed.

Property proper_open: properPset (open(T)).
Proof. apply properPf. Qed.


(* Property of closed sets *)
Property empty_closed: closed(T) (Empty_set _).
Proof. red. eapply properPf. apply empty_compl. apply full_open. Qed.

Property full_closed: closed(T) (Full_set _).
Proof. red. eapply properPf. apply full_compl. apply empty_open. Qed.

Lemma intersects_closed: forall M: PowerEn X,
  ExcludedMiddle -> ForallIn M (closed(T)) -> closed(T) (Intersects M).
Proof with auto.
  intros * EM H.
  red. eapply properPf. rewrite intersects_as_over. apply intersectover_compl...
  apply unions_open. intros U [E []]%im_iff; subst. firstorder.
Qed.

Lemma union_closed: forall U V: Ensemble X, closed(T) U -> closed(T) V -> closed(T) (U \\// V).
Proof. intros. red. eapply properPf. apply union_compl. apply intersect_open; auto. Qed.


Lemma intersect_closed: forall U V: Ensemble X,
  ExcludedMiddle -> closed(T) U -> closed(T) V -> closed(T) (U //\\ V).
Proof with auto. intros. red. eapply properPf.
  apply intersection_compl... apply union_open... Qed.

Lemma proper_closed: properPset (closed(T)).
Proof. intros ? ? ?%(comp_mor). unfold closed. apply properPf. trivial. Qed.

End Topo.

(* ----------------------------------------------------------------- *)
(*                         Topology Basis                            *)
(* ----------------------------------------------------------------- *)

Record isBase {X:Type} (open: Ensemble X -> Prop) : Type := {
  bopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
; bopen_intersect: forall (U V: Ensemble X) x,
  open U -> open V -> x :in: U //\\ V -> exists W, open W /\ x :in: W /\ (W <:= U //\\ V)
}.
Definition Basis (X:Type) := Conded X isBase.
Arguments bopen_cover {X} {open}.
Arguments bopen_intersect {X} {open}.

Record isSubbase {X:Type} (open: Ensemble X -> Prop) : Type := {
  sopen_cover: exists (C: PowerEn X), ForallIn C open /\ cover_all C
}.
Definition Subbasis (X:Type) := Conded X isSubbase.
Arguments sopen_cover {X} {open}.

Section Base.
Context {X:Type}.

(* Obvious lemmas *)
Property topology_is_base (T: Topology X): isBase (open(T)).
Proof with (auto with sets). split.
  - exists ( {' Full_set X '} ).
    split. intros S []. apply (open_empty_total(condPf T)). red...
  - intros. exists (U //\\ V). split... apply (open_intersect(condPf T))...
Qed.

Property base_is_subbase (B: Basis X): isSubbase (open(B)).
Proof with (auto with sets). split. apply (bopen_cover(condPf B)). Qed.

(* Generation *)
Definition topoFromBase (B: PowerEn X): PowerEn X :=
  fun U => forall x, x :in: U -> ExistsIn B (fun V => x :in: V /\ V <:= U).
Property topoFromBase_proper (B: PowerEn X): properPset (topoFromBase B).
Proof. do 3 red. unfold topoFromBase, ExistsIn. intros. rw_refl. Qed.

Lemma base_is_open: forall B, B <:= topoFromBase B.
Proof. intros ? S ? ? ?. exists S. auto with sets. Qed.

Property generate_by_base (B: Basis X): isTopology (topoFromBase (open B)).
Proof with (eauto with sets). split; unfold topoFromBase.
- (* Empty & Full *)
  split; try contradiction.
  destruct (bopen_cover(condPf B)) as [C [? HC]].
  intros ? [U []]%HC %unions_iff. exists U. split... apply H...
- (* Unions *)
  intros ? H ? [U [I0 I1]]%unions_iff. apply H in I1 as HE... clear H.
  destruct HE as [S (? & ? & ?)]. exists S. repeat split...
- (* Intersection *)
  intros ? ? HU HV ? [IU IV]%intersection_iff.
  specialize (HU _ IU) as [S (HU1 & HU2 & HU3)]. specialize (HV _ IV) as [T (HV1 & HV2 & HV3)].
  destruct (bopen_intersect(condPf B) _ _ x HU1 HV1) as [W (H1 & H2 & H3)]...
  exists W. split... split; auto. etransitivity...
Qed.

Lemma open_iff_base_unions: forall (B: Basis X),
  topoFromBase (open B) '= indexed F in PSeton (open B), Unions F.
Proof with (eauto with sets).
  intros. intros U. rewrite indexed_iff. split.
  - (* <:= *)
    intros H.
    exists (unions x in U, fun S => S :in: open(B) /\ x :in: S /\ S <:= U). split.
    + do 2 red. apply inc_forall_unionover_iff. firstorder.
    + rewrite unions_unionover. apply same_set_eq. split.
      * apply inc_forall_unionover_iff. intros ? ?. apply inc_forall_unions_iff. firstorder.
      * intros x Hx. apply unionover_iff. exists x. split...
        apply unions_iff. apply H in Hx as [S ?]. exists S. split... tauto.
  - (* =:> *)
    intros [F (? & E%symmetry)].
    eapply topoFromBase_proper... simpl. do 2 red in H.
    apply (open_union (generate_by_base B)). intros ? ?. apply base_is_open...
Qed.


Definition baseFromSubbase (S: PowerEn X): PowerEn X :=
  indexed L in (List.Forall S), IntersectList L.

Property generate_by_subbase (S: Subbasis X): isBase (baseFromSubbase (open S)).
Proof with (auto with sets).
  split.
  - (* Covers *)
    destruct (sopen_cover(condPf S)) as [C []]. exists C. split...
    intros U A. apply indexed_iff.
    exists (cons U nil). unfold open. split... unfold IntersectList...
  - (* Intersects *)
    intros ? ? ? [LU (AU & EU)]%indexed_r [LV (AV & EV)]%indexed_r HI.
    exists (U //\\ V). split... apply indexed_iff.
    exists (app LU LV). split; [ apply List.Forall_app | ]...
    rewrite <- EU, <- EV. clear AU AV EU EV.
    induction LU; unfold app, IntersectList;
    [ rewrite intersection_comm | rewrite IHLU ]...
Qed.

Program Definition topoByBase (B: Basis X): Topology X := makeCond (topoFromBase (open B)) _.
Next Obligation. split. apply topoFromBase_proper. apply generate_by_base. Qed.

Program Definition baseBySubbase (S: Subbasis X): Basis X := makeCond (baseFromSubbase (open S)) _.
Next Obligation. split. apply properForm_spec. apply generate_by_subbase. Qed.

(*  Denotes is that certain powerset serves as a base of the topology *)
Definition isBaseOf (C: PowerEn X) (T: Topology X): Prop :=
  exists B: Basis X, open(B) = C /\ topoByBase B '= T.
Definition isSubbaseOf (C: PowerEn X) (T: Topology X): Prop :=
  exists S: Subbasis X, open(S) = C /\ topoByBase (baseBySubbase S) '= T.

(* Topology generated by Basis / Subbasis is minimal -> so it is unique *)
Lemma basis_gen_minimal: forall (B: Basis X) (T: Topology X),
  open(B) <:= open(T) -> open(topoByBase B) <:= open(T).
Proof.
  intros ? ? H. unfold topoByBase. simpl.
  rewrite open_iff_base_unions. intros U [F (? & ?%symmetry)]%indexed_r.
  eapply (properPf T); eauto.
  apply (open_union (condPf T)). firstorder.
Qed.

Lemma subbasis_gen_minimal: forall (S: Subbasis X) (T: Topology X),
  open(S) <:= open(T) -> open (topoByBase (baseBySubbase S)) <:= open(T).
Proof.
  intros ? ? H. apply basis_gen_minimal.
  unfold baseBySubbase. simpl. intros F [G (H1 & H2%symmetry)]%indexed_r.
  eapply (properPf T); eauto. clear H2.
  induction G as [| W G]; simpl.
  - apply (open_empty_total(condPf T)).
  - inversion H1; subst. apply (open_intersect (condPf T)); auto. firstorder.
Qed.


Lemma identify_base: forall (T: Topology X) (C: PowerEn X),
  properPset C -> C <:= open(T) ->
  ForallIn (open T) (fun U =>
    forall x, x :in: U -> ExistsIn C (fun V => x :in: V /\ V <:= U)) ->
  isBaseOf C T.
Proof with (eauto with sets).
  intros ? ? HP HI H. destruct (makeCond_pf isBase C) as [B ?].
  - apply HP.
  - (* Is Basis *) split.
    + (* Cover *)
      exists C. split... unfold cover_all.
      intros x [V (? & ? & ?)]%H... apply (open_empty_total(condPf T)).
    + (* Intersection *)
      intros * HU%HI HV%HI IN.
      specialize (open_intersect(condPf T) _ _ HU HV) as HN %H.
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

Property subspace_topo: isTopology (subsetOver (open T)).
Proof with (eauto with sets).
  split; unfold subsetOver.
  - (* Empty & Full *)
    split; apply indexed_iff.
    + exists (Empty_set _). split... apply (open_empty_total (condPf T)).
    + exists (Full_set _). split... apply (open_empty_total (condPf T)).

  - (* Unions *)
    intros. apply indexed_iff.
    exists (Unions (fun U => U :in: open(T) /\ InvIm U incl :in: properForm M)). split.
    + apply (open_union (condPf T)). intros ? []...
    + rewrite unions_as_over. rewrite invim_unionover.
      apply same_set_eq. split.
      * apply inc_forall_unionover_iff. intros U [? [V [? <-]]]...
      * apply inc_forall_unions_iff. intros V HV.
        specialize (H _ HV) as [U [H1 H2]]%indexed_r. rewrite <- H2.
        apply unionover_inc_one with (F := flip InvIm incl).
        split... rewrite H2...

  - (* Intersection *)
    intros U U' [V [HV1 HV2]]%indexed_r [V' [HV'1 HV'2]]%indexed_r.
    apply indexed_iff. exists (V //\\ V'). rewrite invim_intersect.
    split; [apply (open_intersect (condPf T)) | all_rewrite ]...
Qed.

Program Definition SubspaceT: Topology (Subset A) := makeCond (subsetOver (open T)) _.
Next Obligation. split. apply properForm_spec. apply subspace_topo. Qed.


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
  intros. do 6 red in H0. apply indexed_r in H0 as [V []].
  assert (Im U incl '= A //\\ V); [rewrite <- H1|]...
  eapply (properPf T)... apply (open_intersect (condPf T))...
Qed.

Lemma closed_subsp_iff: forall E: Ensemble (Subset A),
  ExcludedMiddle -> ExistsIn (closed(T)) (fun F => InvIm F incl '= E) <-> closed(SubspaceT) E.
Proof with (eauto with sets). intros * EM. split.
  - (* -> *)
    intros [F [HC HE]]. do 2 red in HC. red.
    assert (~! E '= InvIm (~! F) incl). rewrite <- HE. apply invim_compl.
    eapply properPf... apply indexed_def with (F := fun U => InvIm U incl)...
  - (* <- *)
    intros [U [HO HE]]%indexed_r. exists (~! U). split.
    do 2 red. eapply properPf; [apply compl_compl|]...
    rewrite <- invim_compl. rewrite HE. apply compl_compl...
Qed.

Lemma closed_subsp_closed_whole: forall E: Ensemble (Subset A),
  ExcludedMiddle -> closed(T) A -> closed(SubspaceT) E -> closed(T) (Im E incl).
Proof with (eauto with sets). intros * EM HA HE.
  do 7 red in HE. apply indexed_r in HE as [V []].
  assert (E '= InvIm (~! V) incl).
  rewrite <- invim_compl, H0. symmetry. apply compl_compl...
  assert (Im E incl '= A //\\ ~! V). rewrite H1...
  eapply proper_closed... apply intersect_closed...
  eapply proper_open; [apply compl_compl| ]...
Qed.

End Subspace.

(* ----------------------------------------------------------------- *)
(*                        Product Topology                           *)
(* ----------------------------------------------------------------- *)

Section Product.
Context {X:Type} {Y:Type}.
Context (S: Topology X) (T: Topology Y).

Definition prodOver: PowerEn X -> PowerEn Y -> PowerEn (X * Y) :=
  fun C D => indexed P in C ** D, let (U, V) := P in U ** V.

Property prod_basis: isBase (prodOver (open S) (open T)).
Proof with (eauto with sets).
  split; unfold prodOver.
  - (* Covers *)
    exists ( {' Full_set (X * Y) '} ). split.
    + intros ? []. apply indexed_iff. eexists. split. split.
      apply (open_empty_total(condPf S)). apply (open_empty_total(condPf T)). auto...
    + red...

  - (* Intersection *)
    intros T1 T2 x [(U1, V1) [H1 E1]]%indexed_r [(U2, V2) [H2 E2]]%indexed_r H.
    exists (T1 //\\ T2). split; [| all_rewrite]...
    apply prod_iff in H1 as (HU1 & HV1). apply prod_iff in H2 as (HU2 & HV2).
    pose proof (H1 := open_intersect (condPf S) _ _ HU1 HU2).
    pose proof (H2 := open_intersect (condPf T) _ _ HV1 HV2).
    apply indexed_iff. eexists. split. split... rewrite <- E1, <- E2...
Qed.

Program Definition ProductB: Basis (X * Y) := makeCond (prodOver (open S) (open T)) _.
Next Obligation. split. apply properForm_spec. apply prod_basis. Qed.

Definition ProductT: Topology (X * Y) := topoByBase ProductB.


Lemma prod_basis_from_basis: forall (B: PowerEn X) (C: PowerEn Y),
  isBaseOf B S -> isBaseOf C T ->
  isBaseOf (prodOver B C) ProductT.
Proof with (eauto with sets).
  intros * [Bt (? & EB)] [Ct (? & EC)]; subst. apply identify_base.
  - apply properForm_spec.

  - (* Contained in ProductT *)
    etransitivity; [| apply base_is_open].
    intros P [(U, V) (? & ?)]%indexed_r. apply indexed_iff.
    exists (U, V). split... rewrite prod_iff in *. firstorder.

  - (* Defining condition for the basis *)
    intros W HW (x, y) Hxy.
    specialize (HW (x, y) Hxy) as [P [[(U, V) (HI & HE)]%indexed_r (HR1 & HR2)]].
    rewrite <- HE in *.
    apply prod_iff in HI as [HU%EB HV%EC]. apply prod_iff in HR1 as (HU2 & HV2).
    specialize (HU x HU2) as [I (HI1 & HI2)]. specialize (HV y HV2) as [J (HJ1 & HJ2)].
    exists (I ** J). split. apply indexed_iff...
    destruct HI2, HJ2. split; [eauto with sets|].
    etransitivity; eauto...
Qed.


Definition prodSubbasis: PowerEn (X * Y) :=
  (indexed U in open S, InvIm U fst) \\// (indexed V in open T, InvIm V snd).

Theorem prod_subbasis_spec:
  isSubbaseOf prodSubbasis ProductT.
Proof with (eauto with sets).
  destruct (makeCond_pf isSubbase prodSubbasis) as [B HS].
  - (* Proper *)
    do 3 red. intros. unfold prodSubbasis. setoid_rewrite union_iff. rw_refl.

  - (* Subbase (cover) *)
    split. exists ( {' Full_set (X * Y) '} ). split; [| unfold cover_all]...
    intros ? []. left. apply indexed_iff. eexists. split... apply (open_empty_total(condPf S)).

  - (* Generates exact *)
    exists B. split; auto. apply same_set_eq. split.
    + (* open ProductT =:> *)
      apply subbasis_gen_minimal.
      etransitivity; [| apply base_is_open]. unfold open. rewrite HS.
      apply union_incl_split. split.
      all: apply indexed_inced_proper; try apply indexed_spec.
      all: intros ? ?; rewrite invim_fst_prod || rewrite invim_snd_prod.
      all: apply indexed_iff; eexists; split; split...
      apply (open_empty_total(condPf T)). apply (open_empty_total (condPf S)).
    + (* open ProductT <:= *)
      apply basis_gen_minimal. etransitivity; [| apply base_is_open].
      intros P [(U, V) [[HU HV]%prod_iff HP]]%indexed_r. apply indexed_iff.
      exists (cons (InvIm U fst) (cons (InvIm V snd) nil)).
      unfold open. rewrite HS. split.
      * repeat apply List.Forall_cons; [left | right | constructor]...
      * unfold IntersectList. rewrite <- intersection_assoc, prod_invim_split...
Qed.

End Product.

(* The theorem below requires mapping topology over bijective map
Theorem prod_subsp_exch: forall X Y (S: Topology X) (T: Topology Y),
  forall (A: Ensemble X) (B: Ensemble Y),
  open (ProductT (SubspaceT S A) (SubspaceT T B)) '= open (SubspaceT (ProductT S T) (A ** B)).
*)




End ToposSet.

