Require Import UniMMProofs.riscv.

(* ** RISC-V ModelTable *)

(* Same Addr *)

(* Definition  (E : set Event) (e1 e2 : Event) : Prop := *)


Definition R_W_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_read e1 /\ is_write e2 /\ po_loc E e1 e2.

Definition W_W_sa (E : set Event) (e1 e2 : Event) : Prop :=
  is_write e1 /\ is_write e2 /\ po_loc E e1 e2.

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


Definition ModelTable (E : set Event) (e1 e2 : Event) : Prop :=
  R_W_sa E e1 e2 \/ W_W_sa E e1 e2 \/ SC_R_sa E e1 e2 \/ 
  AMO_R_sa E e1 e2 \/ Maq_M E e1 e2 \/ M_Mrl E e1 e2 \/ 
  RCsc_RCsc E e1 e2 \/ LR_SC E e1 e2 \/ Fences E e1 e2 \/ 
  DpAddr E e1 e2 \/ DpData E e1 e2 \/ DpCtrl E e1 e2 .

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


Lemma ModelTable_in_ppo:  forall (E : set Event) (e1 e2 : Event),
  ModelTable E e1 e2 -> ppo E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold ModelTable, ppo in *.
  (* destruct H. *)
  destruct H as [HR_W_sa | [HW_W_sa | [HSC_R_sa | [HAMO_R_sa | [HMaq_M | [HM_Mrl | [HRCsc_RCsc | [HLR_SC | [HFences | [HDpAddr | [HDpData | HDpCtrl]]]]]]]]]]].
  - apply R_W_sa_in_rule1 in HR_W_sa. auto.
  - apply W_W_sa_in_rule1 in HW_W_sa. auto.
  - apply SC_R_sa_in_rule3 in HSC_R_sa. auto.
  - apply AMO_R_sa_in_rule3 in HAMO_R_sa. auto.
  - apply Maq_M_in_rule5 in HMaq_M. right. right. right.  auto.
  - apply M_Mrl_in_rule6 in HM_Mrl. right. right. right. right. right. auto.
  - apply RCsc_RCsc_in_rule7 in HRCsc_RCsc. right. right. right. right. right. auto.
  - apply LR_SC_in_rule8 in HLR_SC. right. right. right. right. right. auto.
  - apply Fences_in_rule4 in HFences. auto.
  - apply DpAddr_in_rule9 in HDpAddr. right. right. right. right. right. right. auto.
  - apply DpData_in_rule10 in HDpData. right. right. right. right. right. right. auto.
  - apply DpCtrl_in_rule11 in HDpCtrl. right. right. right. right. right. right. right. auto.
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