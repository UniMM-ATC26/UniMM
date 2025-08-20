

Require Import ZArith.
Require Import Ensembles.

Require Import Relation_Definitions.


Axiom excluded_middle : forall A, A \/ ~A.
Set Implicit Arguments.

Ltac decide_equality := decide equality; auto with equality arith.

(* Some facts about natural numbers *)
Lemma nat_eq_or_not_eq :
  forall (n1 n2 : nat), n1 = n2 \/ n1 <> n2.
Proof.
  intros n1 n2.
  rewrite <- eq_nat_is_eq.
  destruct (eq_nat_decide n1 n2); auto.
Qed.

Lemma nat_neq_implies_lt :
  forall (n1 n2 : nat), n1 <> n2 -> (n1 < n2 \/ n2 < n1).
Proof.
  intros n1 n2 Hneq.
  generalize (nat_total_order n1 n2).
  intro Htot.
  apply Htot. auto.
Qed.

(** * Events **)
(** ** Events: Definitions *)
Definition Acquire := Set.
Definition Release := Set.

Definition Read := Set. 
Axiom read_eq_or_not_eq :
  forall (r1 r2 : Read), r1 = r2 \/ r1 <> r2.

Definition Write := Set.
Axiom write_eq_or_not_eq :
  forall (w1 w2 : Write), w1 = w2 \/ w1 <> w2.

Definition Rmw := Set.
Axiom rmw_eq_or_not_eq :
  forall (a1 a2 : Rmw), a1 = a2 \/ a1 <> a2.


Definition Fence := Set.
Axiom fence_eq_or_not_eq :
  forall (f1 f2 : Fence), f1 = f2 \/ f1 <> f2.



Inductive Effect :=
  | read : Read -> Effect
  | write : Write -> Effect
  | dom_rmw : Rmw -> Effect
  | codom_rmw : Rmw -> Effect
  | fence : Fence -> Effect.



Definition Id := nat.
Definition Location := nat.
Definition Value := nat.



Record Event := mkev {
  id     : Id;        (* Unique identifier, consistent with program order for a given thread *)
  tid    : Id;        (* Thread identifier *)
  effect : Effect;    (* Effect type (read, write, etc) *)
  loc    : Location;  (* Location accessed by the effect *)
  val    : Value;      (* Value read or written by the effect *)
}.

Definition is_write e : Prop :=
  match effect e with
  | write _ => True
  | codom_rmw _ => True
  | _ => False
  end.

Definition is_read e : Prop :=
  match effect e with
  | read _ => True
  | dom_rmw _ => True
  | _ => False
  end.

Definition is_dom_rmw e : Prop :=
  match effect e with
  | dom_rmw _ => True
  | _ => False
  end.

Definition is_codom_rmw e : Prop :=
  match effect e with
  | codom_rmw _ => True
  | _ => False
  end.

Definition is_fence e : Prop :=
  match effect e with
  | fence _ => True
  | _ => False
  end.



Axiom event_id_uniq : forall e1 e2, e1 <> e2 -> id e1 <> id e2.



(** * Sets and relations ****)
(** ** Sets and relations: Definitions *)

Definition set := Ensemble.
Definition Rln (A:Type) := A -> A -> Prop.

Definition dom (A:Type) (r:Rln A) : set A := fun x => exists y, r x y.
Definition ran (A:Type) (r:Rln A) : set A := fun y => exists x, r x y.

Inductive transitive_closure (r : Rln Event) (e1 e2 : Event) : Prop :=
  | _base : r e1 e2 -> transitive_closure r e1 e2
  | _trans : forall e, r e1 e -> transitive_closure r e e2 -> transitive_closure r e1 e2.

Inductive reflexive_closure (r : Rln Event) : Event -> Event -> Prop :=
  | _refl : forall e, reflexive_closure r e e
  | ref_base : forall e1 e2, r e1 e2 -> reflexive_closure r e1 e2. 



Definition irreflexive (r : Rln Event) : Prop := ~(exists x, r x x).
Definition acyclic (r : Rln Event) : Prop := irreflexive (transitive_closure r).

Definition rel_incl (A:Type) (r1 r2 : Rln A) : Prop :=
  forall x y, r1 x y -> r2 x y.
Definition rel_equal (r1 r2 : Rln Event) : Prop :=
  rel_incl r1 r2 /\ rel_incl r2 r1.
Definition rel_seq (r1 r2 : Rln Event) : Rln Event :=
  fun e1 e2 => exists e, r1 e1 e /\ r2 e e2.
Definition rel_union (r1 r2 : Rln Event) : Rln Event :=
  fun e1 e2 => r1 e1 e2 \/ r2 e1 e2.
Definition maybe r : Rln Event :=
  fun e1 e2 => e1 = e2 \/ r e1 e2.
Definition transitive (A:Type) (r:Rln A) : Prop :=
  (forall x1 x2 x3, (r x1 x2) -> (r x2 x3) -> (r x1 x3)).

Axiom Extensionality_Rlns : forall R1 R2:Rln Event, rel_incl R1 R2 /\ rel_incl R2 R1 -> R1 = R2.

(** ** Sets and relations: Lemmas *)

Lemma tc_trans r e1 e2 e3 :
  transitive_closure r e1 e2 ->
  transitive_closure r e2 e3 ->
  transitive_closure r e1 e3.
Proof.
intros H12 H23; induction H12.
  apply _trans with e2; auto.
  apply _trans with e; auto.
Qed.

Lemma seq_tc_reorg (r1 r2 : Rln Event) x y :
  rel_seq r1 (rel_seq r2 r1) x y ->
  rel_seq (transitive_closure (rel_seq r1 r2)) r1 x y.
Proof.
intros [e1 [Hx1 [e2 [H12 H2y]]]]; exists e2; split; auto; apply _base; exists e1; split; auto.
Qed.

Lemma tc_seq_inv (r1 r2: Rln Event) x z :
  transitive_closure (rel_seq (maybe r1) r2) x z ->
  exists y1, exists y2, (maybe r1) x y1 /\
                        transitive_closure (rel_seq r2 (maybe r1)) y1 y2 /\
                        (maybe r2) y2 z.
Proof.
intro Hxz; induction Hxz. Focus 2.
  destruct H as [y1 [H1y1 Hy1e]]; destruct IHHxz as [e' [y2 [Hee' [He'y2 Hy22]]]].
    exists y1; exists y2; split; auto; split; auto.
    apply _trans with e'; auto; exists e; split; auto.

  destruct H as [y1 [H1y1 Hy12]]; exists y1; exists e2; split; auto; split; [apply _base; exists e2; split; auto; left|left]; auto.
Qed.

Lemma tc_seq_left (r1 r2 : Rln Event) x y z :
  transitive r1 ->
  r1 x y ->
  transitive_closure (rel_seq r1 r2) y z ->
  transitive_closure (rel_seq r1 r2) x z.
Proof.
intros Htr1 Hxy Hyz; induction Hyz. Focus 2.
  apply _trans with e; auto.
    destruct H as [e' [H1' H'e]]; exists e'; split; auto; apply Htr1 with e1; auto.

  apply _base; destruct H as [e' [H1' H'2]]; exists e'; split; auto; apply Htr1 with e1; auto.
Qed.

Lemma tc_seq_right (r1 r2 : Rln Event) x y z :
  transitive r2 ->
  transitive_closure (rel_seq r1 r2) x y ->
  r2 y z ->
  transitive_closure (rel_seq r1 r2) x z.
Proof.
intros Htr2 Hxy Hyz; induction Hxy. Focus 2.
  apply _trans with e; auto.

  apply _base; destruct H as [x [H1x Hx2]]; exists x; split; auto; apply Htr2 with e2; auto.
Qed.

Lemma seq_tc_reorg2 (r1 r2 : Rln Event) x y z :
  transitive r1 ->
  rel_seq r1 (rel_seq r2 r1) x y ->
  rel_seq (transitive_closure (rel_seq r1 r2)) r1 y z ->
  rel_seq (transitive_closure (rel_seq r1 r2)) r1 x z.
Proof.
intros Htr1 [e1 [Hx1 [e2 [H12 H2y]]]]; intros [e3 [Hy3 H3z]]; exists e3; split; auto;
apply tc_trans with e2; auto.
  apply _base; exists e1; auto.
  apply tc_seq_left with y; auto.
Qed.

Lemma tc_seq_incl (r r1 r2 : Rln Event) x y :
  rel_incl r1 r2 ->
  rel_seq (transitive_closure r1) r x y ->
  rel_seq (transitive_closure r2) r x y.
Proof.
intros Hincl [e [Hxe Hey]]; exists e; split; auto; clear Hey; induction Hxe.
  apply _base; apply Hincl; auto.
  apply _trans with e; auto.
Qed.

Lemma tc_seq_reorg (r1 r2 : Rln Event) x y z :
  transitive r1 ->
  transitive_closure (rel_seq r1 (rel_seq r2 r1)) x y ->
  r1 y z ->
  transitive_closure (rel_seq r1 (rel_seq r2 r1)) x z.
Proof.
intros Htr1 Hxy Hyz; induction Hxy.
  destruct H as [e [H1e He2]]; apply _base; exists e; split; auto.
    destruct He2 as [e' [Hee' He'2]]; exists e'; split; auto; apply Htr1 with e2; auto.
  apply _trans with e; auto.
Qed.

Lemma r_in_evts_implies_tc_in_evts (E : set Event) (r : Rln Event) :
  Included _ (Union _ (dom r) (ran r)) E ->
  Included _ (Union _ (dom (transitive_closure r)) (ran (transitive_closure r))) E.
Proof.
intros Hincl _x [x Hdom | y Hran].
  inversion Hdom as [y Htc]; induction Htc.
    apply Hincl; left; exists e2; auto.
    apply Hincl; left; exists e; auto.

  inversion Hran as [x Htc]; induction Htc.
    apply Hincl; right; exists e1; auto.
    apply IHHtc; auto.
Qed.

Lemma tc_incl r1 r2 :
  rel_incl r1 r2 ->
  rel_incl (transitive_closure r1) (transitive_closure r2).
Proof.
intros Hincl x y Hxy; induction Hxy.
  apply _base; apply Hincl; auto.
  apply _trans with e; auto.
Qed.

Lemma seq_tc_seq r1 r2 e1 e2 x y :
  transitive r2 ->
  transitive_closure (rel_seq r1 r2) e1 e2 ->
  maybe (rel_seq r1 r2) e2 x ->
  r2 x y ->
  transitive_closure (rel_seq r1 r2) e1 y.
Proof.
intros Htr2 H12 H2x Hxy.
inversion H2x as [Heq2x | Hs2x]; clear H2x.
  rewrite Heq2x in H12; apply tc_seq_right with x; auto.
  apply tc_trans with e2; auto; apply _base; destruct Hs2x as [e [H2e Hex]];
  exists e; split; auto; apply Htr2 with x; auto.
Qed.

(** * Linear and linear strict orders ****)
(** ** Orders: Definitions *)
Definition partial_order (A:Type) (r:Rln A) (xs:set A) : Prop :=
  Included _(Union _ (dom r) (ran r)) xs /\ (* If an event is in the relation, then it's also in the set *)
  transitive r /\ (* Transitivity *)
  (forall x, ~(r x x)). (* Irreflexivity *)
Ltac destruct_part H := destruct H as [Hinc [Htrans Hirr]].

Definition linear_strict_order (A : Type) (r : Rln A) (xs : set A) : Prop :=
  partial_order r xs /\
  (forall x1 x2,
    (x1 <> x2) -> (xs x1) -> (xs x2) -> (r x1 x2) \/ (r x2 x1)). (* Total *)

Ltac destruct_lin H := destruct H as [Hpart Htot].

Parameter linearisations : Rln Event -> set Event -> set (Rln Event).

Hypothesis order_ext : forall E r,
  partial_order r E ->
  (exists lin_ext, (linearisations r E) lin_ext).

Hypothesis lin_ext_prop : forall E r lin_ext,
  (linearisations r E) lin_ext <->
  rel_incl r lin_ext /\ linear_strict_order lin_ext E.

(** ** Orders: Lemmas *)
Lemma lin_of_big_is_lin_of_little :
  forall (s : set Event) (r1 r2 : Rln Event) (l : Rln Event),
  rel_incl r1 r2 ->
  (linearisations r2 s) l ->
  (linearisations r1 s) l.
Proof.
  intros s r1 r2 l.
  intros Hincl_r1r2 Hlin.
  rewrite lin_ext_prop in Hlin.
  rewrite lin_ext_prop.
  destruct Hlin as [Hincl_r2l Hlin].
  split.
    unfold rel_incl.
    intros e1 e2.
    intro Hinr1.
    generalize (Hincl_r1r2 e1 e2 Hinr1).
    apply Hincl_r2l.
  apply Hlin.
Qed.




(** * Built-in herd relations ****)
(** ** Herd: Definitions*)
Definition internal (E : set Event) (e1 e2 : Event) : Prop := tid e1 = tid e2 /\ E e1 /\ E e2.
Definition external (E : set Event) (e1 e2 : Event) : Prop := ~(internal E e1 e2).

Definition po (E : set Event) (e1 e2 : Event) : Prop := internal E e1 e2 /\ lt (id e1) (id e2).
Definition po_loc (E : set Event) (e1 e2 : Event) : Prop := po E e1 e2 /\ loc e1 = loc e2.

Definition rf (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_read e2 /\ loc e1 = loc e2 /\ val e1 = val e2 /\ E e1 /\ E e2.
Ltac destruct_rf H := destruct H as [Hisw [Hisr [Hloceq [Hvaleq [Hinw Hinr]]]]].
Definition pre_co (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_write e2 /\ loc e1 = loc e2 /\ E e1 /\ E e2.

Definition co (E : set Event) (e1 e2 : Event) : Prop :=
   is_write e1 /\ is_write e2 /\ loc e1 = loc e2  /\ E e1 /\ E e2.

Definition fr (E : set Event) (e1 e2 : Event) : Prop :=
  exists w, is_write w /\ rf E w e1 /\ co E w e2.



Definition rf_well_formed (E : set Event) : Prop :=
  partial_order (rf E) E /\
  forall (r : Event), is_read r ->
    (exists w, rf E w r) /\
    (forall w1 w2, rf E w1 r -> rf E w2 r -> w1 = w2).
Ltac destruct_rf_wf H := destruct H as [Hpart_rf Hex_uni].

Definition is_write_same_loc (l : Location) (e : Event) : Prop :=
  is_write e /\ loc e = l.

Definition co_well_formed (E : set Event)  : Prop :=
  (rel_incl (co E) (pre_co E)) /\
  forall (l : Location),
    linear_strict_order (co E) (Intersection _ E (is_write_same_loc l)).

Definition rfi (E : set Event) (e1 e2 : Event) : Prop := rf E e1 e2 /\ internal E e1 e2.
Definition coi (E : set Event) (e1 e2 : Event) : Prop := co E e1 e2 /\ internal E e1 e2.
Definition fri (E : set Event) (e1 e2 : Event) : Prop :=
 fr E e1 e2 /\ internal E e1 e2.

Definition rfe (E : set Event) (e1 e2 : Event) : Prop := rf E e1 e2 /\ external E e1 e2.
Definition coe (E : set Event) (e1 e2 : Event) : Prop := co E e1 e2 /\ external E e1 e2.
Definition fre (E : set Event) (e1 e2 : Event) : Prop :=
 fr E e1 e2 /\ external E e1 e2.

Definition corf E  (e1 e2 : Event) :=
  exists e, co E e1 e /\ rf E e e2.
Definition corfe E  (e1 e2 : Event) :=
  exists e, co E e1 e /\ rfe E e e2.
Definition coirf E  (e1 e2 : Event) :=
  exists e, coi E e1 e /\ rf E e e2.
Definition coerf E  (e1 e2 : Event) :=
  exists e, coe E e1 e /\ rf E e e2.
Definition coerfe E  (e1 e2 : Event) :=
  exists e, coe E e1 e /\ rfe E e e2.

Definition frrf E  (e1 e2 : Event) :=
  exists e,fr E e1 e /\ rf E e e2.
Definition frrfe E  (e1 e2 : Event) :=
  exists e,fr E e1 e /\ rfe E e e2.
Definition frrfi E  (e1 e2 : Event) :=
  exists e,fr E e1 e /\ rfi E e e2.
Definition frerf E  (e1 e2 : Event) :=
  exists e, fre E e1 e /\ rf E e e2.

Definition complus E e1 e2 := rf E e1 e2 \/ co E e1 e2 \/fr E e1 e2 \/
  rel_seq (co E) (rf E) e1 e2 \/ rel_seq (fr E) (rf E) e1 e2.

(** * X86 axiomatic relations ****)
(** ** X86: Definitions *)


Definition ppo (E : set Event) (e1 e2 : Event) : Prop :=
  po E e1 e2 /\ ((is_write e1 /\ is_write e2) \/ (is_read e1 /\ is_write e2) \/ (is_read e1 /\ is_read e2)).

Definition implied (E : set Event) (e1 e2 : Event) : Prop :=
  po E e1 e2 /\ (is_dom_rmw e2 \/ is_codom_rmw e1).

Definition mfence (E : set Event) (e1 e2 : Event) : Prop :=
  po E e1 e2 /\ (is_fence e1 \/ is_fence e2).

Definition ghb_def (E : set Event)  (e1 e2 : Event) : Prop :=
  co E e1 e2 \/ rfe E e1 e2 \/ fr E e1 e2 \/ ppo E e1 e2 \/ implied E e1 e2 \/ mfence E e1 e2.

Definition ghb_rln  (E : set Event)  : Rln Event :=
  fun e1 e2 => co E e1 e2 \/ rfe E e1 e2 \/ fr E e1 e2 \/ ppo E e1 e2 \/ implied E e1 e2 \/ mfence E e1 e2.

Definition ghb  (E : set Event)  : Prop :=
  acyclic (ghb_rln E).