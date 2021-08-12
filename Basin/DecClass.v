Require Export Decidable.

From Practice Require Import Basin.Base.

Class Dec (P: Prop) :=
  dec_prop: decidable P.

Definition decide (P: Prop) `{Dec P}: decidable P := dec_prop.

Tactic Notation "decides" constr(x) :=
  destruct (decide x).
Tactic Notation "decides" constr(x) "as" simple_intropattern(y) :=
  destruct (decide x) as y.

Instance decT: Dec True.
Proof. apply dec_True. Qed.

Instance decF: Dec False.
Proof. apply dec_False. Qed.


(* Decidable unary predicates *)
Class DecP1 {U:Type} (P: U -> Prop) :=
  dec_p1: forall x:U, decidable (P x).

(* Decidable binary predicates *)
Class DecP2 {U V:Type} (P: U -> V -> Prop) := 
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
Instance deci_p1 {U} (P: U -> Prop) `{DecP1 U P} u: Dec (P u).
Proof. apply dec_p1. Qed.
Instance deci_p2 {U V} (P: U -> V -> Prop) `{DecP2 U V P} u v: Dec (P u v).
Proof. apply dec_p2. Qed.
Instance deci_op1 (F: Prop -> Prop) `{DecOp1 F} P `{Dec P}: Dec (F P).
Proof. apply dec_op1. trivial. Qed.
Instance deci_op2 (F: Prop -> Prop -> Prop) `{DecOp2 F} P Q `{Dec P} `{Dec Q}: Dec (F P Q).
Proof. apply dec_op2; trivial. Qed.


(* Decidable Setoids *)
Class DecSetoid {U} `(S : Setoid U) :=
  setoid_dec : forall x y : U, decidable (x == y).

Instance decp_seq U `{DecSetoid U}: DecP2 equiv.
Proof. intros ? ?. apply setoid_dec. Qed.

Class UsualEqDec U := {
  usual_setoid :> UsualSetoid U
; usual_dec :> DecSetoid (setoid_usual U _)
}.


(* Notation to consider implication as an operator *)
Notation "A '-> B" := (impl A B) (at level 100, right associativity).

#[export]
Hint Unfold impl: core.


(* Typeclass mechanics for decidability of 1-predicate *)
Class DecPred1 {U:Type} (P: U -> Prop) :=
  dec_pr1: forall x, decidable (P x).

Instance decpr1_const {U} P `{Dec P}: @DecPred1 U (const P).
Proof. intros ?. auto. Qed.

Instance decpr1_p1 {U T} P `{DecP1 U P} (t: T -> U):
  DecPred1 (fun x => P (t x)).
Proof. intros ?. auto. Qed.

Instance decpr1_p2 {U V T} P `{DecP2 U V P} (s: T -> U) (t: T -> V):
  DecPred1 (fun x => P (s x) (t x)).
Proof. intros ?. auto. Qed.

Instance decpr1_op1 {U} F `{DecOp1 F} (P: U -> Prop) `(DecPred1 U P):
  DecPred1 (fun x => F (P x)).
Proof. intros ?. auto. Qed.

Instance decpr1_op2 {U} F `{DecOp2 F} (P Q: U -> Prop) `(DecPred1 U P) `(DecPred1 U Q):
  DecPred1 (fun x => F (P x) (Q x)).
Proof. intros ?. auto. Qed.

(* Specialize to Dec *)
(* Instance dec_decpr {U} P (x: U) `{DecPred1 U P}: (Dec (P x)).
Proof. apply dec_pr1. Qed. *)


(* Marks witness-search as decidable *)
(* Perhaps equivalent to excluded middle, but at least feels better this way *)
Axiom DecExists: forall U (P: U -> Prop), DecPred1 P -> Dec (exists x, P x).

Lemma DecForall: forall U (P: U -> Prop), DecPred1 P -> Dec (forall x, P x).
Proof. intros. apply (decpr1_op1 not) in H as H0. apply DecExists in H0 as [[x H0] | H0].
  - right. intros ?. auto.
  - left. intros x. destruct (H x). auto. exfalso. eauto.
Qed.

Instance decp_exists {U} P `{DecPred1 U P}: Dec (exists x, P x).
Proof. apply DecExists. trivial. Qed.

Instance decp_forall {U} P `{DecPred1 U P}: Dec (forall x, P x).
Proof. apply DecForall. trivial. Qed.


(* Below may not be used *)

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



(* ----------------------------------------------------------------- *)
(*                Proof Irrelevance with minimal axioms              *)
(* ----------------------------------------------------------------- *)

(* Follows the proof outline of Coq.Logic.Berardi *)
Section ProofIrrelevance.

Let IFProp {P:Prop} (B:Prop) `{Dec B} (e1 e2: P) :=
  match decide B with
  | or_introl _ => e1
  | or_intror _ => e2
  end.

(* AoC on disjunction *)
Lemma AC_IF: forall (P B:Prop) `{Dec B} (e1 e2:P) (Q:P -> Prop),
  (B -> Q e1) -> (~ B -> Q e2) -> Q (IFProp B e1 e2).
Proof. intros. unfold IFProp.
  destruct (decide B); auto. Qed.

Variable Bool: Prop.
Variable T: Bool.
Variable F: Bool.
Context `{Dec Bool}.

Let pow (P:Prop) := P '-> Bool.

Local Instance dec_pow P `{Dec P}: Dec (pow P).
Proof. apply dec_imp; auto. Qed.

(* Another axiom weaker than EM *)
Axiom ProofDecidable: forall P: Prop, decidable P -> forall p1 p2: P, decidable (p1 = p2). 

Local Instance dec_proof (P: Prop) `{Dec P}: @DecP2 P P eq.
Proof. intros ? ?. apply ProofDecidable. trivial. Qed.

Section Retracts.
  Variables A B: Prop.

  Record retract: Prop :=
    {i: A -> B; j: B -> A; inv: forall a:A, j (i a) = a}.
  Record retract_cond: Prop :=
    {i2: A -> B; j2: B -> A; inv2: retract -> forall a:A, j2 (i2 a) = a}.

  Lemma AC: forall r:retract_cond, retract -> forall a:A, j2 r (i2 r a) = a.
  Proof. apply inv2. Qed.

  Local Instance dec_retract `{Dec A} `{Dec B}: Dec retract.
  Proof.
    assert (D: Dec (exists (i: A -> B) (j: B -> A), forall a:A, j (i a) = a)). {
      apply DecExists. intros i.
      apply DecExists. intros j.
      apply DecForall. exact _.
    }
    destruct D as [(i, (j, ?))|].
    left. econstructor; eauto.
    right. intros []. firstorder.
  Qed.

  Local Instance dec_retract_cond `{Dec A} `{Dec B}: Dec retract_cond.
  Proof.
    assert (D: Dec (exists (i: A -> B) (j: B -> A), retract '-> forall a:A, j (i a) = a)). {
      apply DecExists. intros i.
      apply DecExists. intros j.
      apply dec_imp; apply dec_prop.
    }
    destruct D as [(i, (j, ?))|].
    left. econstructor; eauto.
    right. intros []. firstorder.
  Qed.

End Retracts.

Arguments i {A} {B}.
Arguments j {A} {B}.
Arguments i2 {A} {B}.
Arguments j2 {A} {B}.

(* Commutation of implication & existential quantification *)
Lemma L1: forall (A B:Prop) `{Dec A} `{Dec B}, retract_cond (pow A) (pow B).
Proof. intros.
  assert (Dec (retract (pow A) (pow B))) as [[i j HR]|HR].
  apply dec_retract; exact _.
  - exists i j. trivial.
  - exists (fun _ _ => F) (fun _ _ => F). contradiction.
Qed.


(* Paradox set *)
Let U := forall (P:Prop) `(Dec P), pow P.

Local Instance dec_U: Dec U.
Proof. unfold U.
  apply DecForall. intros ?.
  apply DecForall. intros ?.
  apply dec_prop.
Qed.

Let f (u:U) : pow U := u U _.

Let g (h:pow U) : U :=
  fun X _ => let lX := j2 (L1 X U) in let rU := i2 (L1 U U) in lX (rU h).

Lemma retract_pow_U_U : retract (pow U) U.
Proof. exists g f.
  intros ?. unfold f, g.
  apply AC.
  exists id id. auto.
Qed.

Local Instance dec_proof_p (P: Prop) `{Dec P} (p q: P): Dec (p = q).
Proof. apply ProofDecidable. trivial. Qed.

(* Russel paradox encoding *)
Let Not_b (b:Bool) := IFProp (b = T) F T.

Let R : U := g (fun u:U => Not_b (u U _ u)).

Lemma not_has_fixpoint : R U _ R = Not_b (R U _ R).
Proof.
  unfold R at 1. unfold g.
  rewrite AC. reflexivity.
  exists id id. auto.
Qed.

Theorem classical_proof_irrelevance : T = F.
Proof.
  generalize not_has_fixpoint. unfold Not_b.
  apply AC_IF.
  - intros [] []. reflexivity.
  - contradiction.
Qed.

End ProofIrrelevance.

Lemma subs_eq_iff: forall U (P: U -> Prop) `(DecPred1 _ P) (x y: sig P),
  get x = get y <-> x = y.
Proof. intros. split.
  - intros E. destruct x as [x' p], y as [y' q]. simpl in E; subst.
    f_equal. apply classical_proof_irrelevance. apply H.
  - intros ?. f_equal. trivial.
Qed.

(* Proof irrelevance gives usual setoid for subset *)
Instance usual_subset U `(UsualSetoid U) (P: U -> Prop): UsualSetoid {x | P x}. Qed.

Program Instance usual_dec_subset U `(UsualEqDec U) (P: U -> Prop) `(DecPred1 _ P):
  UsualEqDec {x | P x}.
Next Obligation with trivial.
  intros ? ?. simpl. red. rewrite <- subs_eq_iff...
  pose (D := decide (get x == get y))...
Qed.


Program Instance usual_dec_prod U V `(UsualEqDec U) `(UsualEqDec V):
  UsualEqDec (U * V).
Next Obligation.
  intros (x, x') (y, y'). simpl. unfold decidable.
  rewrite pair_equal_spec. pose proof (decide (x == y /\ x' == y')). trivial.
Qed.
