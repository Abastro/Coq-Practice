Require Export Decidable.

From Practice Require Import Basin.Base.


Generalizable All Variables.

Class Dec (P: Prop) :=
  dec_prop: decidable P.

Definition decide P `{Dec P}: decidable P := dec_prop.


Tactic Notation "decides" constr(x) :=
  destruct (decide x).
Tactic Notation "decides" constr(x) "as" simple_intropattern(y) :=
  destruct (decide x) as y.

Ltac contra := match goal with
  | [ |- ?R ] => let c := fresh "contra" in decides R as [|c]; [easy | exfalso]
  end.

Instance decT: Dec True.
Proof. apply dec_True. Qed.

Instance decF: Dec False.
Proof. apply dec_False. Qed.


(* Decidable unary predicates *)
Class DecP1 `(P: U -> Prop) :=
  dec_p1: forall x:U, decidable (P x).

(* Decidable binary predicates *)
Class DecP2 `(P: U -> V -> Prop) := 
  dec_p2: forall (x:U) (y:V), decidable (P x y).

(* Decidable unary prop-operators *)
Class DecOp1 (F: Prop -> Prop) :=
  dec_op1: forall P:Prop, decidable P -> decidable (F P).

(* Decidable binary prop-operators *)
Class DecOp2 (F: Prop -> Prop -> Prop) :=
  dec_op2: forall P Q:Prop, decidable P -> decidable Q -> decidable (F P Q).

Instance decop_and: DecOp2 and.
Proof. intros ? ?. apply dec_and. Qed.
Instance decop_or: DecOp2 or.
Proof. intros ? ?. apply dec_or. Qed.
Instance decop_not: DecOp1 not.
Proof. intros ?. apply dec_not. Qed.

Instance decop_impl: DecOp2 impl.
Proof. intros ? ?. apply dec_imp. Qed.
Instance decop_iff: DecOp2 iff.
Proof. intros ? ?. apply dec_iff. Qed.


(* Translation into Dec instance *)
Instance deci_p1 `(P: U -> Prop) `(DecP1 U P) u: Dec (P u).
Proof. apply dec_p1. Qed.
Instance deci_p2 `(P: U -> V -> Prop) `(DecP2 U V P) u v: Dec (P u v).
Proof. apply dec_p2. Qed.
Instance deci_op1 (F: Prop -> Prop) `(DecOp1 F) `(Dec P): Dec (F P).
Proof. apply dec_op1. trivial. Qed.
Instance deci_op2 (F: Prop -> Prop -> Prop) `(DecOp2 F) `(Dec P) `(Dec Q): Dec (F P Q).
Proof. apply dec_op2; trivial. Qed.


(* Decidable Setoids *)
Class DecSetoid `(S: Setoid U) :=
  setoid_dec : forall x y : U, decidable (x == y).

Instance decp_seq `(DecSetoid U): DecP2 equiv.
Proof. intros ? ?. apply setoid_dec. Qed.

Class UsualEqDec U := {
  usual_setoid :> UsualSetoid U
; usual_dec :> DecSetoid (setoid_usual _)
}.

Instance decp2_usualeq `(UsualEqDec U): DecP2 (@eq U).
Proof. intros x y. decides (x == y); firstorder. Qed.


(* Propagating decidable equality *)
Program Instance usual_dec_sig `(UsualEqDec U) (P: U -> Prop):
  UsualEqDec {x | P x}.
Next Obligation with auto.
  intros ? ?. simpl. red. rewrite sig_eq_iff...
  decides (get x = get y)...
Qed.

Program Instance usual_dec_prod `(UsualEqDec U) `(UsualEqDec V):
  UsualEqDec (U * V).
Next Obligation with auto.
  intros (x, y) (x', y'). simpl. unfold decidable.
  rewrite pair_equal_spec. decides (x == x' /\ y == y')...
Qed.


(* Notation to consider implication as an operator *)
Notation "A '-> B" := (impl A B) (at level 100, right associativity).

#[export]
Hint Unfold impl: core.


(* Typeclass mechanics for decidability of 1-predicate *)
Class DecPred1 `(P: U -> Prop) :=
  dec_pr1: forall x, decidable (P x).

Instance decpr1_const {U} P `(Dec P): @DecPred1 U (const P).
Proof. intros ?. auto. Qed.

Instance decpr1_p1 {U} P `(DecP1 U P) `(t: T -> U):
  DecPred1 (fun x => P (t x)).
Proof. intros ?. auto. Qed.

Instance decpr1_p2 {U V} P `(DecP2 U V P) `(s: T -> U) `(t: T -> V):
  DecPred1 (fun x => P (s x) (t x)).
Proof. intros ?. auto. Qed.

Instance decpr1_op1 {U} F `(DecOp1 F) `(P: U -> Prop) `(DecPred1 U P):
  DecPred1 (fun x => F (P x)).
Proof. intros ?. auto. Qed.

Instance decpr1_op2 {U} F `(DecOp2 F) (P Q: U -> Prop) `(DecPred1 U P) `(DecPred1 U Q):
  DecPred1 (fun x => F (P x) (Q x)).
Proof. intros ?. auto. Qed.


(* Index type where any existence could be searched *)
Class Findable (J: Type): Prop :=
  findEx: forall P: J -> Prop, DecP1 P -> Dec (exists a, P a).

Instance decp_exists `(Findable J) `(DecPred1 J P): Dec (exists a, P a).
Proof. apply findEx. trivial. Qed.

Instance decp_forall `(F: Findable J) `(D: DecPred1 J P): Dec (forall a, P a).
Proof with eauto.
  apply (decpr1_op1 not _) in D as K. apply F in K as [(i, K)|K].
  - right... - left. intros i. destruct (D i)... exfalso...
Qed.


Instance findable_bool: Findable bool.
Proof with eauto.
  intros P DP.
  decides (P false \/ P true) as [H|]. destruct H; left...
  right. intros [[] ?]...
Qed.


Instance findable_sum `(Findable J) `(Findable K): Findable (J + K).
Proof with eauto.
  intros P DP.
  decides (exists j, P (inl j)) as [[j Hj]|Hl]. left...
  decides (exists k, P (inr k)) as [[k Hk]|Hr]. left...
  right. intros [[] ?]...
Qed.

Instance findable_prod `(Findable J) `(Findable K): Findable (J * K).
Proof with eauto.
  intros P DP.
  destruct (@decide (exists j k, P (j, k))) as [(? & ? & ?)|]. {
    apply decp_exists... intros ?. apply dec_prop.
  } left...
  right. intros [[] ?]...
Qed.



(*
  Problem of naive witness-search

  Proposition decexists_excluded_middle:
    (forall U (P: U -> Prop), inhabited U -> DecPred1 P -> Dec (exists x, P x)) ->
    forall P: Prop, Dec P.
  Proof.
    intros DE *.
    set (U := option P).
    set (F := (fun p: U => match p with Some _ => True | None => False end) ).
    assert (Dec (exists pf: U, F pf)) as [[pf H]|H]. {
      apply DE. constructor. exact None.
      intros []; apply dec_prop. }
    - destruct pf as [pf|]; try contradiction. left. exact pf.
    - right. intros pf. apply H. exists (Some pf). simpl. trivial.
  Qed.
*)


(*
  Below not used
(* Using typeclass mechanics to infer decidability of predicate *)
Class DecPred (l: Tlist) (P: predicate l) :=
  dec_pred: predicate_all l (pointwise_ext decidable l P).

(*
Instance decpr_const {U l} P `{DecPred l P}: DecPred (Tcons U l) (const P).
Proof. intros ?. auto. Qed.
*)

Instance decpr_const {l} P `{Dec P}: DecPred l (generalize_all l P).
Proof. induction l. auto. intros ?. simpl. apply IHl. Qed.

Instance decpr_def P `{Dec P}: DecPred Tnil P.
Proof. auto. Qed.

Instance decpr_p1 {U l} P `{DecP1 U P} (x: arrows l U):
  DecPred l (pointwise_ext P l x).
Proof. induction l. apply H. intros ?. simpl. apply IHl. Qed.

Instance decpr_p2 {U V l} P `{DecP2 U V P} (x: arrows l U) (y: arrows l V):
  DecPred l (pointwise_ext2 P l x y).
Proof. induction l. apply H. intros ?. simpl. apply IHl. Qed.

Instance decpr_op1 {l} F `{DecOp1 F} (P: predicate l) `{DecPred l P}:
  DecPred l (pointwise_ext F l P).
Proof. induction l. apply H, H0. intros ?. simpl. apply IHl, H0. Qed.

Instance decpr_op2 {l} F `{DecOp2 F} (P Q: predicate l) `{DecPred l P} `{DecPred l Q}:
  DecPred l (pointwise_ext2 F l P Q).
Proof. induction l. apply H; [apply H0 | apply H1].
  intros ?. simpl. apply IHl; [apply H0 | apply H1]. Qed.


Instance decp_exists_l (l: Tlist) P `{DecPred l P}: Dec (predicate_exists l P).
Proof. induction l. auto. simpl. apply DecExists. intros ?. apply IHl. apply H. Qed.

Instance decp_forall_l (l: Tlist) P `{DecPred l P}: Dec (predicate_all l P).
Proof. induction l. auto. simpl. apply DecForall. intros ?. apply IHl. apply H. Qed.
*)

