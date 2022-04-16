(* ----------------------------------------------------------------- *)
(*                      Evaluable Finite Graphs                      *)
(* ----------------------------------------------------------------- *)

From Practice Require Import Base Evaluable.
From mathcomp Require Export path fingraph.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.


Lemma filter_enum (T: finType) A: filter A (enum T) = enum A.
Proof. rewrite enumT //. Qed.

Lemma tnth_zip `(t: n.-tuple T) `(u: n.-tuple U) i:
  tnth (zip_tuple t u) i = (tnth t i, tnth u i).
Proof.
  rewrite /tnth. move: (tnth_default (zip_tuple t u))=> [d e].
  rewrite nth_zip ?size_tuple // -!tnth_nth //.
Qed.


Section Graph.
Variable n: nat.

Definition graph := n.-tuple (seq 'I_n).

Definition grrel (G: graph) := grel (tnth G).
Definition relgraph (r: rel 'I_n) :=
  tupleOf [fun i => filter (r i) (enumOrd n)].

Property relgraph_rgraph r: relgraph r = tupleOf (rgraph r).
Proof. rewrite /relgraph !evals enumT. apply/eq_mktuple=> i //. Qed.

Property relgraphK r: grrel (relgraph r) =2 r.
Proof.
  rewrite relgraph_rgraph /grrel /grel=> i j /=.
  rewrite evals tnth_mktuple -rgraphK //.
Qed.


Definition grwf (G: graph): graph :=
  relgraph (grrel G).


(* Assume well-formed graph *)
Definition grincl (G K: graph) :=
  all [pred gk | subseq gk.1 gk.2] (zip_tuple G K).

Lemma grincl_rel G K i j: grincl G K -> grrel G i j -> grrel K i j.
Proof.
  move=> /all_tnthP /(_ i) /=.
  rewrite tnth_zip /=. by move/mem_subseq /(_ j).
Qed.



(* Graph addition *)
Definition gradd (G K: graph) :=
  grwf (map_tuple [fun gk => gk.1 ++ gk.2] (zip_tuple G K)).

Property graddK G K: grrel (gradd G K) =2 [rel i j | grrel G i j || grrel K i j].
Proof.
  move=> i j. rewrite relgraphK /=.
  rewrite tnth_map tnth_zip /=. apply/mem_cat.
Qed.


Definition transCl (G: graph): graph :=
  tupleOf (dfs (tnth G) n [::]).

Lemma transClP G x y:
  reflect (exists2 p, path (grrel G) x p & y = last x p)
  (grrel (transCl G) x y).
Proof.
  rewrite /grrel /transCl !evals /=.
  rewrite tnth_mktuple.
  have := (@dfsP _ (tnth G) x y). by rewrite card_ord.
Qed.

Lemma transCl_trans G: transitive (grrel (transCl G)).
Proof.
  move=> x y z /transClP[p ep ->] /transClP[q eq ->]. apply/transClP.
  exists (p ++ q); by [rewrite cat_path ep eq | rewrite last_cat].
Qed.

Lemma transCl_conn0 G x: grrel (transCl G) x x.
Proof. apply/transClP. by exists [::]. Qed.

Lemma transCl_conn1 G x y: grrel G x y -> grrel (transCl G) x y.
Proof. move=> /= H. apply/transClP. exists [:: y]; rewrite /= ?H //. Qed.

End Graph.


Section Image.
Variable m n: nat.
Variable f: 'I_m -> 'I_n.

Definition graphpre (G: graph n): graph m :=
  tupleOf (fun a => filter [preim f of tnth G (f a)] (enumOrd m)).

Definition graphim (G: graph m): graph n :=
  tupleOf (fun x => [seq f b |
    a <- (filter [preim f of pred1 x] (enumOrd m)),
    b <- tnth G a
  ]).


Property graphpre_rel G x y: grrel (graphpre G) x y <->
  grrel G (f x) (f y).
Proof. rewrite /= /graphpre !evals tnth_mktuple filter_enum mem_enum //. Qed.

Property graphim_rel G a b: grrel (graphim G) a b <->
  exists x y, a = f x /\ b = f y /\ grrel G x y.
Proof.
  rewrite /= /graphim !evals tnth_mktuple filter_enum.
  split.
  - move/flatten_mapP=> [x].
    rewrite mem_enum=> /eqP <- /mapP[y Hy ->].
    by exists x, y.
  - move=> [x [] y] [->] [->] Hy. apply/flatten_mapP.
    exists x. rewrite mem_enum. by apply/eqP.
    apply/mapP. by exists y.
Qed.


Section InjImage.
Hypothesis If: injective f.

(* TODO Later move to more general *)
Lemma preim_pred1 a: [preim f of pred1 (f a)] =1 pred1 a.
Proof. move=> i /=. by apply /inj_eq. Qed.

Lemma graph_im_pre G: graphpre (graphim G) = grwf G.
Proof.
  apply/eq_from_tnth=> a.
  rewrite /graphpre /graphim /grwf /relgraph !evals !tnth_mktuple /=.
  apply/eq_filter=> b /=.
  under eq_filter=> i do rewrite preim_pred1.
  have ->: filter (pred1 a) (enum 'I_m) = [:: a] by rewrite enumT -enum1 //.
  rewrite /= cats0. by apply/mem_map.
Qed.

End InjImage.

End Image.


