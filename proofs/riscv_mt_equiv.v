Require Import UniMMProofs.riscv.

(* ** RISC-V ModelTable *)

(* Same Addr *)

(* Definition  (E : set Event) (e1 e2 : Event) : Prop := *)


Definition R_W_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_write e2 /\ po_loc E e1 e2.

Definition W_W_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_write e2 /\ po_loc E e1 e2.

Definition R_R_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_read e2 /\ po_loc_no_w E e1 e2 /\ ~ rsw E e1 e2.

Definition po_loc_not_fence (E : set Event) : Prop :=
  forall e1 e2, po_loc E e1 e2 -> ~ is_fence e1 /\ ~ is_fence e2.

Definition SC_R_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_x e1 /\ is_write e1 /\ is_read e2 /\ rfi E e1 e2.

Definition AMO_R_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_amo e1 /\ is_read e2 /\ rfi E e1 e2.

Definition Maq_M (E : set Event) (e1 e2 : Event) : Prop :=
  is_acquire e1 /\ po E e1 e2.

Definition M_Mrl (E : set Event) (e1 e2 : Event) : Prop :=
  is_release e2 /\ po E e1 e2.

Definition RCsc_RCsc (E : set Event) (e1 e2 : Event) : Prop :=
  RCsc e1 /\ RCsc e2 /\ po E e1 e2.

Definition LR_SC (E : set Event) (e1 e2 : Event) : Prop :=
  po E e1 e2 /\ is_x e1 /\ is_read e2 /\ is_x e2 /\ is_write e2.

Definition Fences (E : set Event) (e1 e2 : Event) : Prop :=
  (fence_r_r E e1 e2 /\ is_read e1 /\ is_read e2) \/ (fence_r_w E e1 e2 /\ is_read e1 /\ is_write e2) \/ (fence_r_rw E e1 e2 /\ is_read e1) \/
  (fence_w_r E e1 e2 /\ is_write e1 /\ is_read e2) \/ (fence_w_w E e1 e2 /\ is_write e1 /\ is_write e2) \/ (fence_w_rw E e1 e2 /\ is_write e1) \/
  (fence_rw_r E e1 e2 /\ is_read e2) \/ (fence_rw_w E e1 e2 /\ is_write e2) \/ (fence_rw_rw E e1 e2) \/
  (fence_tso E e1 e2 /\ ((is_write e1 /\ is_write e2) \/ is_read e1)).

Definition DpAddr (E : set Event) (e1 e2 : Event) : Prop :=
  addr E e1 e2.

Definition DpData (E : set Event) (e1 e2 : Event) : Prop :=
  data E e1 e2 /\ is_write e2.
  
Definition DpCtrl (E : set Event) (e1 e2 : Event) : Prop :=
  ctrl E e1 e2 /\ is_write e2.

Definition M_W_R (E : set Event) (e1 e2 : Event) : Prop :=
  exists e, (addr E e1 e \/ data E e1 e) /\ rfi E e e2 /\ is_write e /\ is_read e2.

Definition M_M_W  (E : set Event) (e1 e2 : Event) : Prop :=
  exists e, addr E e1 e /\ po E e e2 /\ is_write e2.


Definition ModelTable (E : set Event) (e1 e2 : Event) : Prop :=
  R_W_sa E e1 e2 \/ W_W_sa E e1 e2 \/ R_R_sa E e1 e2 \/ SC_R_sa E e1 e2 \/
  AMO_R_sa E e1 e2 \/ Maq_M E e1 e2 \/ M_Mrl E e1 e2 \/ 
  RCsc_RCsc E e1 e2 \/ LR_SC E e1 e2 \/ Fences E e1 e2 \/ 
  DpAddr E e1 e2 \/ DpData E e1 e2 \/ DpCtrl E e1 e2 \/ M_W_R E e1 e2 \/ M_M_W E e1 e2 .

Lemma R_W_sa_in_rule1: forall (E : set Event) (e1 e2 : Event),
  R_W_sa E e1 e2 -> rule1 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_W_sa, rule1 in *.
  simpl.
  destruct H as [_ [Hwrite Hpo]]. auto.
Qed.

Lemma W_W_sa_in_rule1: forall (E : set Event) (e1 e2 : Event),
  W_W_sa E e1 e2 -> rule1 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold W_W_sa, rule1 in *.
  simpl.
  destruct H as [_ [Hwrite Hpo]]. auto.
Qed.

Lemma R_R_sa_in_rule2: forall (E : set Event) (e1 e2 : Event),
  R_R_sa E e1 e2 -> rule2 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold R_R_sa, rule2 in *.
  auto.
Qed.

Lemma SC_R_sa_in_rule3: forall (E : set Event) (e1 e2 : Event),
  SC_R_sa E e1 e2 -> rule3 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold SC_R_sa, rule3 in *.
  destruct H as [Hx [Hwrite [Hread Hrfi]]].
  split.
  - exact Hrfi.
  - split.
    + right. exact Hx.
    + exact Hread.
Qed.

Lemma AMO_R_sa_in_rule3: forall (E : set Event) (e1 e2 : Event),
  AMO_R_sa E e1 e2 -> rule3 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold AMO_R_sa, rule3 in *.
  destruct H as [Hamo [Hread Hrfi]].
  split.
  - exact Hrfi.
  - split.
    + left. exact Hamo.
    + exact Hread.
Qed.

Lemma Maq_M_in_rule5: forall (E : set Event) (e1 e2 : Event),
  Maq_M E e1 e2 -> rule5 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Maq_M, rule5 in *.
  destruct H as [Haq Hpo]. auto.
Qed.

Lemma M_Mrl_in_rule6: forall (E : set Event) (e1 e2 : Event),
  M_Mrl E e1 e2 -> rule6 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_Mrl, rule6 in *.
  destruct H as [Haq Hpo]. auto.
Qed.

Lemma RCsc_RCsc_in_rule7: forall (E : set Event) (e1 e2 : Event),
  RCsc_RCsc E e1 e2 -> rule7 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold RCsc_RCsc, rule7 in *.
  destruct H as [Hrc1 [Hrc2 Hpo]]. auto.
Qed.

Lemma LR_SC_in_rule8: forall (E : set Event) (e1 e2 : Event),
  LR_SC E e1 e2 -> rule8 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold LR_SC, rule8 in *. 
  auto.
Qed.

Lemma Fences_in_rule4: forall (E : set Event) (e1 e2 : Event),
  Fences E e1 e2 -> rule4 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Fences, rule4 in *. 
  auto.
Qed.

Lemma DpAddr_in_rule9: forall (E : set Event) (e1 e2 : Event),
  DpAddr E e1 e2 -> rule9 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpAddr, rule9 in *. 
  auto.
Qed.

Lemma DpData_in_rule10: forall (E : set Event) (e1 e2 : Event),
  DpData E e1 e2 -> rule10 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpData, rule10 in *. 
  auto.
Qed.

Lemma DpCtrl_in_rule11: forall (E : set Event) (e1 e2 : Event),
  DpCtrl E e1 e2 -> rule11 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpCtrl, rule11 in *. 
  auto.
Qed.

Lemma M_W_R_in_rule12: forall (E : set Event) (e1 e2 : Event),
  M_W_R E e1 e2 -> rule12 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_W_R, rule12 in *.
  auto.
Qed.

Lemma M_M_W_in_rule13: forall (E : set Event) (e1 e2 : Event),
  M_M_W E e1 e2 -> rule13 E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_M_W, rule13 in *.
  auto.
Qed.


Lemma ModelTable_in_ppo:  forall (E : set Event) (e1 e2 : Event),
  ModelTable E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold ModelTable, ppo in *.
  destruct H as [HR_W_sa | [HW_W_sa | [HR_R_sa | [HSC_R_sa | [HAMO_R_sa | [HMaq_M | [HM_Mrl | [HRCsc_RCsc | [HLR_SC | [HFences | [HDpAddr | [HDpData | [HDpCtrl | [HM_W_R | HM_M_W]]]]]]]]]]]]]].
  - left. apply R_W_sa_in_rule1. auto.
  - left. apply W_W_sa_in_rule1. auto.
  - right. left. apply R_R_sa_in_rule2. auto.
  - right. right. left. apply SC_R_sa_in_rule3. auto.
  - right. right. left. apply AMO_R_sa_in_rule3. auto.
  - right. right. right. right. left. apply Maq_M_in_rule5. auto.
  - right. right. right. right. right. left. apply M_Mrl_in_rule6. auto.
  - right. right. right. right. right. right. left. apply RCsc_RCsc_in_rule7. auto.
  - right. right. right. right. right. right. right. left. apply LR_SC_in_rule8. auto.
  - right. right. right. left. apply Fences_in_rule4. auto.
  - right. right. right. right. right. right. right. right. left. apply DpAddr_in_rule9. auto.
  - right. right. right. right. right. right. right. right. right. left. apply DpData_in_rule10. auto.
  - right. right. right. right. right. right. right. right. right. right. left. apply DpCtrl_in_rule11. auto.
  - right. right. right. right. right. right. right. right. right. right. right. left. apply M_W_R_in_rule12. auto.
  - right. right. right. right. right. right. right. right. right. right. right. right. apply M_M_W_in_rule13. auto.
Qed.

Lemma rule1_in_R_W_sa_or_W_W_sa_mt: forall (E : set Event) (e1 e2 : Event),
  po_loc_not_fence E -> rule1 E e1 e2 -> R_W_sa E e1 e2 \/ W_W_sa E e1 e2.
Proof.
  intros E e1 e2 Hpo_loc_not_fence Hrule1.
  unfold rule1 in Hrule1.
  destruct Hrule1 as [Hwrite_e2 Hpo_loc].
  destruct (Hpo_loc_not_fence e1 e2 Hpo_loc) as [Hnot_fence_e1 _].
  destruct (memacc e1) eqn:Hmemacc_e1.
  - left. unfold R_W_sa, is_read. rewrite Hmemacc_e1. auto.
  - right. unfold W_W_sa, is_write. rewrite Hmemacc_e1. auto.
  - left. unfold R_W_sa, is_read. rewrite Hmemacc_e1. auto.
  - exfalso. apply Hnot_fence_e1. unfold is_fence. rewrite Hmemacc_e1. auto.
Qed.

Lemma rule2_in_R_R_sa_mt: forall (E : set Event) (e1 e2 : Event),
  rule2 E e1 e2 -> R_R_sa E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold rule2, R_R_sa in *.
  auto.
Qed.

Lemma rule3_in_SC_R_sa_or_AMO_R_sa_mt: forall (E : set Event) (e1 e2 : Event),
  rule3 E e1 e2 -> SC_R_sa E e1 e2 \/ AMO_R_sa E e1 e2.
Proof.
  intros E e1 e2 Hrule3.
  unfold rule3 in Hrule3.
  destruct Hrule3 as [Hrfi [Hamo_or_x Hread_e2]].
  destruct Hamo_or_x as [Hamo_e1 | Hx_e1].
  - right. unfold AMO_R_sa. auto.
  - left. unfold SC_R_sa.
    assert (Hwrite_e1 : is_write e1).
    { destruct Hrfi as [Hrf _].
      unfold rf in Hrf.
      tauto. }
    auto.
Qed.

Lemma rule4_in_Fences_mt: forall (E : set Event) (e1 e2 : Event),
  rule4 E e1 e2 -> Fences E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Fences, rule4 in *.
  auto.
Qed.

Lemma rule5_in_Maq_M_mt: forall (E : set Event) (e1 e2 : Event),
  rule5 E e1 e2 -> Maq_M E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Maq_M, rule5 in *.
  destruct H as [Hpo Hacquire].
  auto.
Qed.

Lemma rule6_in_M_Mrl_mt: forall (E : set Event) (e1 e2 : Event),
  rule6 E e1 e2 -> M_Mrl E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_Mrl, rule6 in *.
  destruct H as [Hpo Hrelease].
  auto.
Qed.

Lemma rule7_in_RCsc_RCsc_mt: forall (E : set Event) (e1 e2 : Event),
  rule7 E e1 e2 -> RCsc_RCsc E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold RCsc_RCsc, rule7 in *.
  destruct H as [Hpo [Hrc1 Hrc2]].
  auto.
Qed.

Lemma rule8_in_LR_SC_mt: forall (E : set Event) (e1 e2 : Event),
  rule8 E e1 e2 -> LR_SC E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold LR_SC, rule8 in *.
  auto.
Qed.

Lemma rule9_in_DpAddr_mt: forall (E : set Event) (e1 e2 : Event),
  rule9 E e1 e2 -> DpAddr E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpAddr, rule9 in *.
  auto.
Qed.

Lemma rule10_in_DpData_mt: forall (E : set Event) (e1 e2 : Event),
  rule10 E e1 e2 -> DpData E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpData, rule10 in *.
  auto.
Qed.

Lemma rule11_in_DpCtrl_mt: forall (E : set Event) (e1 e2 : Event),
  rule11 E e1 e2 -> DpCtrl E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpCtrl, rule11 in *.
  auto.
Qed.

Lemma rule12_in_M_W_R_mt: forall (E : set Event) (e1 e2 : Event),
  rule12 E e1 e2 -> M_W_R E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_W_R, rule12 in *.
  auto.
Qed.

Lemma rule13_in_M_M_W_mt: forall (E : set Event) (e1 e2 : Event),
  rule13 E e1 e2 -> M_M_W E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_M_W, rule13 in *.
  auto.
Qed.

Lemma ppo_in_ModelTable: forall (E : set Event) (e1 e2 : Event),
  po_loc_not_fence E -> ppo E e1 e2 -> ModelTable E e1 e2.
Proof.
  intros E e1 e2 Hpo_loc_not_fence H.
  unfold ppo in H.
  destruct H as [Hrule1 | [Hrule2 | [Hrule3 | [Hrule4 | [Hrule5 | [Hrule6 | [Hrule7 | [Hrule8 | [Hrule9 | [Hrule10 | [Hrule11 | [Hrule12 | Hrule13]]]]]]]]]]]].
  - apply rule1_in_R_W_sa_or_W_W_sa_mt in Hrule1; auto.
    destruct Hrule1 as [HR_W_sa | HW_W_sa].
    + unfold ModelTable. left. auto.
    + unfold ModelTable. right. left. auto.
  - unfold ModelTable. right. right. left.
    apply rule2_in_R_R_sa_mt. auto.
  - apply rule3_in_SC_R_sa_or_AMO_R_sa_mt in Hrule3.
    destruct Hrule3 as [HSC_R_sa | HAMO_R_sa].
    + unfold ModelTable. right. right. right. left. auto.
    + unfold ModelTable. right. right. right. right. left. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. right. right. left.
    apply rule4_in_Fences_mt. auto.
  - unfold ModelTable. right. right. right. right. right. left.
    apply rule5_in_Maq_M_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. left.
    apply rule6_in_M_Mrl_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. left.
    apply rule7_in_RCsc_RCsc_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. right. left.
    apply rule8_in_LR_SC_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. right. right. right. left.
    apply rule9_in_DpAddr_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. right. right. right. right. left.
    apply rule10_in_DpData_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. right. right. right. right. right. left.
    apply rule11_in_DpCtrl_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. right. right. right. right. right. right. left.
    apply rule12_in_M_W_R_mt. auto.
  - unfold ModelTable. right. right. right. right. right. right. right. right. right. right. right. right. right. right.
    apply rule13_in_M_M_W_mt. auto.
Qed.

Lemma ModelTable_eq_ppo: forall (E : set Event),
  po_loc_not_fence E -> rel_equal (ModelTable E) (ppo E).
Proof.
  intros E Hpo_loc_not_fence.
  split.
  - unfold rel_incl. intros e1 e2 H. apply ModelTable_in_ppo. auto.
  - unfold rel_incl. intros e1 e2 H. apply ppo_in_ModelTable; auto.
Qed.

(* Definition main_model  (E : set Event)  : Prop :=
  acyclic (fun e1 e2 => main_model_def E e1 e2). *)

(* Definition test_model_def (E : set Event)   (e1 e2 : Event) : Prop :=
  co E e1 e2 \/ rfe E e1 e2 \/ fr E e1 e2 \/ rule3 E e1 e2.

Definition test_model_rln (E : set Event)  : Rln Event :=
  fun e1 e2 => co E e1 e2 \/ rfe E e1 e2 \/ fr E e1 e2 \/ rule3 E e1 e2.

Definition test_model  (E : set Event)  : Prop :=
  acyclic (test_model_rln E). *)

(* Definition test_model  (E : set Event)  : Prop :=
  acyclic (fun e1 e2 => test_model_def E e1 e2). *)

Definition ModelTable_model_rln (E : set Event)  : Rln Event :=
  fun e1 e2 => co E e1 e2 \/ rfe E e1 e2 \/ fr E e1 e2 \/ ModelTable E e1 e2.

Definition ModelTable_model  (E : set Event)  : Prop :=
  acyclic (ModelTable_model_rln E).

(* ** Memory Model Proofs*)

Lemma rule3_implies_ppo : forall (E : set Event) (e1 e2 : Event),
  rule3 E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 Hrule3.
  unfold ppo.
  right. right. left. exact Hrule3.
Qed.



Lemma ModelTable_in_main_rln :  forall (E : set Event)  ,
  rel_incl (ModelTable_model_rln E) (main_model_rln E).
Proof.
  intros E x y H.
  unfold main_model_rln, ModelTable_model_rln in *.

  destruct H as [Hco | [Hrfe | [Hfr | Hrule3]]].
  - left. apply Hco. 
  - right. left. apply Hrfe. 
  - right. right. left. apply Hfr.
  - right. right. right. apply ModelTable_in_ppo. auto. 
Qed.

Lemma main_rln_in_ModelTable : forall (E : set Event),
  po_loc_not_fence E -> rel_incl (main_model_rln E) (ModelTable_model_rln E).
Proof.
  intros E Hpo_loc_not_fence x y H.
  unfold main_model_rln, ModelTable_model_rln in *.
  destruct H as [Hco | [Hrfe | [Hfr | Hppo]]].
  - left. auto.
  - right. left. auto.
  - right. right. left. auto.
  - right. right. right. apply ppo_in_ModelTable; auto.
Qed.

Lemma ModelTable_model_rln_eq_main_model_rln : forall (E : set Event),
  po_loc_not_fence E -> rel_equal (ModelTable_model_rln E) (main_model_rln E).
Proof.
  intros E Hpo_loc_not_fence.
  split.
  - apply ModelTable_in_main_rln.
  - apply main_rln_in_ModelTable. auto.
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



Theorem ModelTable_model_acyclic_if_main_model_acyclic :
  forall (E : set Event) ,
    rel_incl (ModelTable_model_rln E) (main_model_rln E) -> main_model E -> ModelTable_model E.
Proof.
  intros E.
  apply r1_acyclic_if_r2_acyclic.
Qed.

Theorem ModelTable_model_iff_main_model :
  forall (E : set Event),
    po_loc_not_fence E -> (ModelTable_model E <-> main_model E).
Proof.
  intros E Hpo_loc_not_fence.
  unfold ModelTable_model, main_model.
  split.
  - apply r1_acyclic_if_r2_acyclic.
    apply main_rln_in_ModelTable. auto.
  - apply r1_acyclic_if_r2_acyclic.
    apply ModelTable_in_main_rln.
Qed.
