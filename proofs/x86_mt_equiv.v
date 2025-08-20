Require Import UniMMProofs.x86.

(* ** X86 ModelTable *)

(* Same Addr *)

Definition R_R_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_read e2 /\ po_loc E e1 e2.

Definition R_W_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_write e2 /\ po_loc E e1 e2.

Definition W_W_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_write e2 /\ po_loc E e1 e2.

Definition Rmw_R_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_codom_rmw e1 /\ is_read e2 /\ po_loc E e1 e2.

Definition Rmw_W_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_codom_rmw e1 /\ is_write e2 /\ po_loc E e1 e2.

Definition R_Rmw_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_dom_rmw e2 /\ po_loc E e1 e2.

Definition W_Rmw_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_dom_rmw e2 /\ po_loc E e1 e2.

(* Diff Addr *)

Definition R_R_da (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_read e2 /\ po E e1 e2.

Definition R_W_da (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_write e2 /\ po E e1 e2.

Definition W_W_da (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_write e2 /\ po E e1 e2.

Definition Rmw_R_da (E : set Event) (e1 e2 : Event) : Prop :=
  is_codom_rmw e1 /\ is_read e2 /\ po E e1 e2.

Definition Rmw_W_da (E : set Event) (e1 e2 : Event) : Prop :=
  is_codom_rmw e1 /\ is_write e2 /\ po E e1 e2.

Definition R_Rmw_da (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_dom_rmw e2 /\ po E e1 e2.

Definition W_Rmw_da (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_dom_rmw e2 /\ po E e1 e2.

Definition mfence_mt_left (E : set Event) (e1 e2: Event) : Prop :=
  po E e1 e2 /\ is_fence e2.

Definition mfence_mt_right (E : set Event) (e1 e2: Event) : Prop :=
  po E e1 e2 /\ is_fence e1.


Definition X86ModelTable (E : set Event) (e1 e2 : Event) : Prop :=
  R_R_sa E e1 e2 \/ R_W_sa E e1 e2 \/ W_W_sa E e1 e2 \/ 
  Rmw_R_sa E e1 e2 \/ Rmw_W_sa E e1 e2 \/ R_Rmw_sa E e1 e2 \/ 
  W_Rmw_sa E e1 e2 \/ 
  R_R_da E e1 e2 \/ R_W_da E e1 e2 \/ W_W_da E e1 e2 \/ 
  Rmw_R_da E e1 e2 \/ Rmw_W_da E e1 e2 \/ 
  R_Rmw_da E e1 e2 \/ W_Rmw_da E e1 e2 \/ 
  mfence_mt_left E e1 e2 \/ mfence_mt_right E e1 e2.

Definition X86ModelTable_rln (E : set Event)  : Rln Event :=
  fun e1 e2 => co E e1 e2 \/ rfe E e1 e2 \/ fr E e1 e2 \/ X86ModelTable E e1 e2.

Definition X86ModelTable_ghb (E : set Event)  : Prop :=
  acyclic (X86ModelTable_rln E).

Lemma R_R_sa_in_ppo: forall (E : set Event) (e1 e2 : Event),
  R_R_sa E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_R_sa, ppo, po_loc in *.
  destruct H as [Hread1 [Hread2 Hpo_loc]].
  destruct Hpo_loc as [Hpo _].
  split.
  - exact Hpo.
  - right. right. split; assumption.
Qed.

Lemma R_W_sa_in_ppo: forall (E : set Event) (e1 e2 : Event),
  R_W_sa E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_W_sa, ppo, po_loc in *.
  destruct H as [Hread [Hwrite Hpo_loc]].
  destruct Hpo_loc as [Hpo _].
  split.
  - exact Hpo.
  - right. left. split; assumption.
Qed.

Lemma W_W_sa_in_ppo: forall (E : set Event) (e1 e2 : Event),
  W_W_sa E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold W_W_sa, ppo, po_loc in *.
  destruct H as [Hwrite1 [Hwrite2 Hpo_loc]].
  destruct Hpo_loc as [Hpo _].
  split.
  - exact Hpo.
  - left. split; assumption.
Qed.

Lemma R_R_da_in_ppo: forall (E : set Event) (e1 e2 : Event),
  R_R_da E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_R_da, ppo in *.
  destruct H as [Hread1 [Hread2 Hpo]].
  split.
  - exact Hpo.
  - right. right. split; assumption.
Qed.

Lemma R_W_da_in_ppo: forall (E : set Event) (e1 e2 : Event),
  R_W_da E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_W_da, ppo in *.
  destruct H as [Hread [Hwrite Hpo]].
  split.
  - exact Hpo.
  - right. left. split; assumption.
Qed.

Lemma W_W_da_in_ppo: forall (E : set Event) (e1 e2 : Event),
  W_W_da E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold W_W_da, ppo in *.
  destruct H as [Hwrite1 [Hwrite2 Hpo]].
  split.
  - exact Hpo.
  - left. split; assumption.
Qed.

Lemma mfence_mt_left_in_mfence: forall (E : set Event) (e1 e2 : Event),
  mfence_mt_left E e1 e2 -> mfence E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold mfence_mt_left in H.
  destruct H as [Hpo Hfence].
  unfold mfence.
  split; [exact Hpo | right; exact Hfence].
Qed.

Lemma mfence_mt_right_in_mfence: forall (E : set Event) (e1 e2 : Event),
  mfence_mt_right E e1 e2 -> mfence E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold mfence_mt_right in H.
  destruct H as [Hpo Hfence].
  unfold mfence.
  split; [exact Hpo | left; exact Hfence].
Qed.

Lemma Rmw_R_sa_in_implied: forall (E : set Event) (e1 e2 : Event),
  Rmw_R_sa E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Rmw_R_sa, implied, po_loc in *.
  destruct H as [Hcodom [Hread Hpo_loc]].
  destruct Hpo_loc as [Hpo _].
  split.
  - exact Hpo.
  - right. exact Hcodom.
Qed.


Lemma Rmw_W_sa_in_implied: forall (E : set Event) (e1 e2 : Event),
  Rmw_W_sa E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Rmw_W_sa, implied, po_loc in *.
  destruct H as [Hcodom [Hwrite Hpo_loc]].
  destruct Hpo_loc as [Hpo _].
  split.
  - exact Hpo.
  - right. exact Hcodom.
Qed.


Lemma R_Rmw_sa_in_implied: forall (E : set Event) (e1 e2 : Event),
  R_Rmw_sa E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_Rmw_sa, implied, po_loc in *.
  destruct H as [Hread [Hdom Hpo_loc]].
  destruct Hpo_loc as [Hpo _].
  split.
  - exact Hpo.
  - left. exact Hdom.
Qed.

Lemma W_Rmw_sa_in_implied: forall (E : set Event) (e1 e2 : Event),
  W_Rmw_sa E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold W_Rmw_sa, implied, po_loc in *.
  destruct H as [Hwrite [Hdom Hpo_loc]].
  destruct Hpo_loc as [Hpo _].
  split.
  - exact Hpo.
  - left. exact Hdom.
Qed.

Lemma Rmw_R_da_in_implied: forall (E : set Event) (e1 e2 : Event),
  Rmw_R_da E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Rmw_R_da, implied in *.
  destruct H as [Hcodom [Hread Hpo]].
  split.
  - exact Hpo.
  - right. exact Hcodom.
Qed.

Lemma Rmw_W_da_in_implied: forall (E : set Event) (e1 e2 : Event),
  Rmw_W_da E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Rmw_W_da, implied in *.
  destruct H as [Hcodom [Hwrite Hpo]].
  split.
  - exact Hpo.
  - right. exact Hcodom.
Qed.

Lemma R_Rmw_da_in_implied: forall (E : set Event) (e1 e2 : Event),
  R_Rmw_da E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_Rmw_da, implied in *.
  destruct H as [Hread [Hdom Hpo]].
  split.
  - exact Hpo.
  - left. exact Hdom.
Qed.

Lemma W_Rmw_da_in_implied: forall (E : set Event) (e1 e2 : Event),
  W_Rmw_da E e1 e2 -> implied E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold W_Rmw_da, implied in *.
  destruct H as [Hwrite [Hdom Hpo]].
  split.
  - exact Hpo.
  - left. exact Hdom.
Qed.


Lemma X86ModelTable_in_ghb_rln :  forall (E : set Event)  ,
  rel_incl (X86ModelTable_rln E) (ghb_rln E).
Proof.
  intros E e1 e2 H.
  unfold X86ModelTable_rln, ghb_rln in H.
  destruct H as [Hco | [Hrfe | [Hfr | HX]]].
  - left. exact Hco.
  - right. left. exact Hrfe.
  - right. right. left. exact Hfr.
  - unfold X86ModelTable in HX.
    destruct HX as [HX|HX]; [apply R_R_sa_in_ppo in HX; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply R_W_sa_in_ppo in HX; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply W_W_sa_in_ppo in HX; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply Rmw_R_sa_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply Rmw_W_sa_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply R_Rmw_sa_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply W_Rmw_sa_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply R_R_da_in_ppo in HX; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply R_W_da_in_ppo in HX; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply W_W_da_in_ppo in HX; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply Rmw_R_da_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply Rmw_W_da_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply R_Rmw_da_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply W_Rmw_da_in_implied in HX; right; right; right; right; left; exact HX|
    destruct HX as [HX|HX]; [apply mfence_mt_left_in_mfence in HX; right; right; right; right; right; exact HX|
    apply mfence_mt_right_in_mfence in HX; right; right; right; right; right; exact HX
    ]]]]]]]]]]]]]]].
Qed.

Lemma r1_acyclic_if_r2_acyclic : forall (r1 r2 : Rln Event),
  rel_incl r1 r2 -> acyclic r2 -> acyclic r1.

Proof.
  intros r1 r2 Hincl Hacyc.
  unfold acyclic in *.
  unfold irreflexive in *.
  intros Htc.
  destruct Htc as [x Htc'].
  apply tc_incl in Hincl.
  apply Hincl in Htc'.
  assert (H : exists y, transitive_closure r2 y y).
  { exists x. apply Htc'. }
  apply Hacyc in H.
  contradiction.
Qed.

Theorem X86ModelTable_acyclic_if_ghb_acyclic :
  forall (E : set Event) ,
    rel_incl (X86ModelTable_rln E) (ghb_rln E) -> ghb E -> X86ModelTable_ghb E.
Proof.
  intros E.
  apply r1_acyclic_if_r2_acyclic.
Qed.


Lemma ppo_in_R_R_da_or_R_W_da_or_W_W_da :
  forall (E : set Event) (e1 e2 : Event),
    ppo E e1 e2 ->
      R_R_da E e1 e2 
      \/ R_W_da E e1 e2 
      \/ W_W_da E e1 e2.
Proof.
  intros E e1 e2 Hppo.
  unfold ppo in Hppo.
  destruct Hppo as [Hpo Htypes].
  destruct Htypes as [HWW | [HRW | HRR]].
  
  - destruct HWW as [Hw1 Hw2].
    right. right.
    unfold W_W_da.
    split; [exact Hw1 | split; [exact Hw2 | exact Hpo]].
  
  - destruct HRW as [Hr1 Hw2].
    right. left.
    unfold R_W_da.
    split; [exact Hr1 | split; [exact Hw2 | exact Hpo]].
  
  - destruct HRR as [Hr1 Hr2].
    left.
    unfold R_R_da.
    split; [exact Hr1 | split; [exact Hr2 | exact Hpo]].
Qed.

Lemma dom_rmw_not_fence : forall e, is_dom_rmw e -> ~is_fence e.
Proof.
  unfold is_dom_rmw, is_fence.
  intros e Hdom.
  destruct (effect e) eqn:Heff.
  all: simpl in Hdom; try contradiction; auto.
Qed.

Lemma codom_rmw_not_fence : forall e, is_codom_rmw e -> ~is_fence e.
Proof.
  unfold is_codom_rmw, is_fence.
  intros e Hcodom.
  destruct (effect e) eqn:Heff.
  all: simpl in Hcodom; try contradiction; auto.
Qed.

Lemma event_type_trichotomy : forall e,
  is_read e \/ is_write e \/ is_fence e.
Proof.
  intro e.
  unfold is_read, is_write, is_fence.
  destruct (effect e) eqn:Heff.
  - left. simpl. trivial.
  - right. left. simpl. trivial.
  - left. simpl. trivial.
  - right. left. simpl. trivial.
  - right. right. simpl. trivial.
Qed.


Axiom implied_no_fence : forall E e1 e2,
  implied E e1 e2 -> ~is_fence e1 /\ ~is_fence e2.


Lemma implied_no_fence_e1 : forall E e1 e2,
  implied E e1 e2 -> ~is_fence e1.
Proof.
  intros E e1 e2 Himplied.
  apply (implied_no_fence E e1 e2 Himplied).
Qed.

Lemma implied_no_fence_e2 : forall E e1 e2,
  implied E e1 e2 -> ~is_fence e2.
Proof.
  intros E e1 e2 Himplied.
  apply (implied_no_fence E e1 e2 Himplied).
Qed.


Lemma implied_in_Rmw_R_da_or_Rmw_W_da_or_R_Rmw_da_or_W_Rmw_da :
  forall (E : set Event) (e1 e2 : Event),
    implied E e1 e2 ->
      Rmw_R_da E e1 e2
      \/ Rmw_W_da E e1 e2
      \/ R_Rmw_da E e1 e2
      \/ W_Rmw_da E e1 e2.
Proof.
  intros E e1 e2 Himplied.
  unfold implied in Himplied.
  destruct Himplied as [Hpo Hrmw].
  destruct Hrmw as [Hdom_e2 | Hcodom_e1].
  
  - 
    assert (Hread_e2 : is_read e2).
    { unfold is_read, is_dom_rmw in *.
      destruct (effect e2) eqn:Heff; simpl in Hdom_e2; try contradiction.
      simpl. trivial. }
    
    generalize (event_type_trichotomy e1); intro Htype_e1.
    destruct Htype_e1 as [Hread_e1 | [Hwrite_e1 | Hfence_e1]].
    + 
      right. right. left.
      unfold R_Rmw_da.
      split; [exact Hread_e1 | split; [exact Hdom_e2 | exact Hpo]].
    + 
      right. right. right.
      unfold W_Rmw_da.
      split; [exact Hwrite_e1 | split; [exact Hdom_e2 | exact Hpo]].
    + 
      exfalso.
      
      assert (Himplied_reconstruct : implied E e1 e2).
      { unfold implied. split; [exact Hpo | left; exact Hdom_e2]. }
      apply (implied_no_fence_e1 E e1 e2 Himplied_reconstruct Hfence_e1).
  
  
  - 
    assert (Hwrite_e1 : is_write e1).
    { unfold is_write, is_codom_rmw in *.
      destruct (effect e1) eqn:Heff; simpl in Hcodom_e1; try contradiction.
      simpl. trivial. }
    
   
    generalize (event_type_trichotomy e2); intro Htype_e2.
    destruct Htype_e2 as [Hread_e2 | [Hwrite_e2 | Hfence_e2]].
    + 
      left.
      unfold Rmw_R_da.
      split; [exact Hcodom_e1 | split; [exact Hread_e2 | exact Hpo]].
    + 
      right. left.
      unfold Rmw_W_da.
      split; [exact Hcodom_e1 | split; [exact Hwrite_e2 | exact Hpo]].
    + 
      exfalso.
      assert (Himplied_reconstruct : implied E e1 e2).
      { unfold implied. split; [exact Hpo | right; exact Hcodom_e1]. }
      apply (implied_no_fence_e2 E e1 e2 Himplied_reconstruct Hfence_e2).
Qed.


Lemma mfence_in_mfence_mt_left_or_right :
  forall (E : set Event) (e1 e2 : Event),
    mfence E e1 e2 ->
      mfence_mt_left E e1 e2 \/ mfence_mt_right E e1 e2.
Proof.
  intros E e1 e2 Hmfence.
  unfold mfence in Hmfence.
  destruct Hmfence as [Hpo Hfence_or].
  destruct Hfence_or as [Hfence_e1 | Hfence_e2].
  
  - right.
    unfold mfence_mt_right.
    split; [exact Hpo | exact Hfence_e1].
  
  - left.
    unfold mfence_mt_left.
    split; [exact Hpo | exact Hfence_e2].
Qed.
  
Lemma ghb_in_X86ModelTable_rln :  forall (E : set Event)  ,
  rel_incl (ghb_rln E) (X86ModelTable_rln E).
Proof.
  intros E e1 e2 H.
  unfold ghb_rln, X86ModelTable_rln in *.
  destruct H as [Hco | [Hrfe | [Hfr | [Hppo | [Himplied | Hmfence]]]]].
  

  - left. exact Hco.
  

  - right. left. exact Hrfe.
  

  - right. right. left. exact Hfr.
  

  - right. right. right.
    apply ppo_in_R_R_da_or_R_W_da_or_W_W_da in Hppo.
    unfold X86ModelTable.
    destruct Hppo as [HR_R_da | [HR_W_da | HW_W_da]].
    + (* R_R_da case *)
      do 7 right. left. exact HR_R_da.
    + (* R_W_da case *)
      do 8 right. left. exact HR_W_da.
    + (* W_W_da case *)
      do 9 right. left. exact HW_W_da.
  
  (* Case: implied E e1 e2 *)
  - right. right. right.
    apply implied_in_Rmw_R_da_or_Rmw_W_da_or_R_Rmw_da_or_W_Rmw_da in Himplied.
    unfold X86ModelTable.
    destruct Himplied as [HRmw_R_da | [HRmw_W_da | [HR_Rmw_da | HW_Rmw_da]]].
    + (* Rmw_R_da case *)
      do 10 right. left. exact HRmw_R_da.
    + (* Rmw_W_da case *)
      do 11 right. left. exact HRmw_W_da.
    + (* R_Rmw_da case *)
      do 12 right. left. exact HR_Rmw_da.
    + (* W_Rmw_da case *)
      do 13 right. left. exact HW_Rmw_da.
  
  (* Case: mfence E e1 e2 *)
  - right. right. right.
    apply mfence_in_mfence_mt_left_or_right in Hmfence.
    unfold X86ModelTable.
    destruct Hmfence as [Hmfence_left | Hmfence_right].
    + (* mfence_mt_left case *)
      do 14 right. left. exact Hmfence_left.
    + (* mfence_mt_right case *)
      do 15 right. exact Hmfence_right.
Qed.

Theorem ghb_acyclic_if_X86ModelTable_acyclic :
  forall (E : set Event) ,
    rel_incl (ghb_rln E) (X86ModelTable_rln E) -> X86ModelTable_ghb E -> ghb E.
Proof.
  intros E.
  apply r1_acyclic_if_r2_acyclic.
Qed.


Theorem ghb_rln_equiv_X86ModelTable_rln :
  forall (E : set Event),
    rel_equal (ghb_rln E) (X86ModelTable_rln E).
Proof.
  intros E.
  split.
  - apply ghb_in_X86ModelTable_rln.
  - apply X86ModelTable_in_ghb_rln.
Qed.


Theorem ghb_equiv_X86ModelTable_ghb :
  forall (E : set Event),
    ghb E <-> X86ModelTable_ghb E.
Proof.
  intros E.
  unfold ghb, X86ModelTable_ghb.
  split.
  
 
  - intro Hghb_acyc.
    
    generalize (ghb_rln_equiv_X86ModelTable_rln E); intro Hequiv.
    unfold rel_equal in Hequiv.
    destruct Hequiv as [Hincl1 Hincl2].
    apply (r1_acyclic_if_r2_acyclic (X86ModelTable_rln E) (ghb_rln E) Hincl2 Hghb_acyc).
  
  - intro HX86_acyc.
    
    generalize (ghb_rln_equiv_X86ModelTable_rln E); intro Hequiv.
    unfold rel_equal in Hequiv.
    destruct Hequiv as [Hincl1 Hincl2].
    apply (r1_acyclic_if_r2_acyclic (ghb_rln E) (X86ModelTable_rln E) Hincl1 HX86_acyc).
Qed.