Require Import UniMMProofs.riscv.
Require Import UniMMProofs.riscv_mt_equiv.



Lemma riscv_event_mem_type_cases : forall e,
  is_read e \/ is_write e \/ is_fence e.
Proof.
  intro e.
  unfold is_read, is_write, is_fence.
  destruct (memacc e) eqn:Heff.
  - left. simpl. trivial.  
  - right. left. simpl. trivial. 
  - left. simpl. trivial.  
  - right. right. simpl. trivial.  
Qed.


Axiom fence_no_po_loc : forall E e1 e2,
  po_loc E e1 e2 -> ~is_fence e1 /\ ~is_fence e2.


Axiom x_implies_write_or_read : forall e,
  is_x e -> is_write e \/ is_read e.


Axiom x_in_rfi_implies_write : forall E e1 e2,
  rfi E e1 e2 -> is_x e1 -> is_write e1.

Lemma rule1_in_R_W_sa_or_W_W_sa: forall (E : set Event) (e1 e2 : Event),
  rule1 E e1 e2 -> R_W_sa E e1 e2 \/ W_W_sa E e1 e2.
Proof.
  intros E e1 e2 Hrule1.
  unfold rule1 in Hrule1.
  destruct Hrule1 as [Hwrite_e2 Hpo_loc].
  

  assert (Hno_fence : ~is_fence e1 /\ ~is_fence e2).
  { apply (fence_no_po_loc E e1 e2 Hpo_loc). }
  destruct Hno_fence as [Hno_fence_e1 Hno_fence_e2].
  

  generalize (riscv_event_mem_type_cases e1); intro Htype_e1.
  destruct Htype_e1 as [Hread_e1 | [Hwrite_e1 | Hfence_e1]].
  
  - left.
    unfold R_W_sa.
    split; [exact Hread_e1 | split; [exact Hwrite_e2 | exact Hpo_loc]].
  
  - right.
    unfold W_W_sa.
    split; [exact Hwrite_e1 | split; [exact Hwrite_e2 | exact Hpo_loc]].
  
  - exfalso.
    apply Hno_fence_e1.
    exact Hfence_e1.
Qed.

Lemma rule2_in_R_R_sa: forall (E : set Event) (e1 e2 : Event),
  rule2 E e1 e2 -> R_R_sa E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold rule2, R_R_sa in *.
  auto.
Qed.



Lemma rule3_in_SC_R_sa_or_AMO_R_sa: forall (E : set Event) (e1 e2 : Event),
  rule3 E e1 e2 -> SC_R_sa E e1 e2 \/ AMO_R_sa E e1 e2.
Proof.
  intros E e1 e2 Hrule3.
  unfold rule3 in Hrule3.
  destruct Hrule3 as [Hrfi [Hamo_or_x Hread_e2]].
  

  destruct Hamo_or_x as [Hamo_e1 | Hx_e1].
  
  - right.
    unfold AMO_R_sa.
    split; [exact Hamo_e1 | split; [exact Hread_e2 | exact Hrfi]].
  
  - left.
    unfold SC_R_sa.
    assert (Hwrite_e1 : is_write e1).
    { apply (x_in_rfi_implies_write E e1 e2); assumption. }
    
    split; [exact Hx_e1 | split; [exact Hwrite_e1 | split; [exact Hread_e2 | exact Hrfi]]].
Qed.

Lemma rule4_in_Fences: forall (E : set Event) (e1 e2 : Event),
  rule4 E e1 e2 -> Fences E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Fences, rule4 in *. 
  auto.
Qed.

Lemma rule5_in_Maq_M: forall (E : set Event) (e1 e2 : Event),
  rule5 E e1 e2 -> Maq_M E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold Maq_M, rule5 in *.
  destruct H as [Haq Hpo]. auto.
Qed.

Lemma rule6_in_M_Mrl: forall (E : set Event) (e1 e2 : Event),
  rule6 E e1 e2 -> M_Mrl E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_Mrl, rule6 in *.
  destruct H as [Haq Hpo]. auto.
Qed.

Lemma rule7_in_RCsc_RCsc: forall (E : set Event) (e1 e2 : Event),
  rule7 E e1 e2 -> RCsc_RCsc E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold RCsc_RCsc, rule7 in *.
  destruct H as [Hrc1 [Hrc2 Hpo]]. auto.
Qed.

Lemma rule8_in_LR_SC: forall (E : set Event) (e1 e2 : Event),
  rule8 E e1 e2 -> LR_SC E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold LR_SC, rule8 in *. 
  auto.
Qed.

Lemma rule9_in_DpAddr: forall (E : set Event) (e1 e2 : Event),
  rule9 E e1 e2 -> DpAddr E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpAddr, rule9 in *. 
  auto.
Qed.

Lemma rule10_in_DpData: forall (E : set Event) (e1 e2 : Event),
  rule10 E e1 e2 -> DpData E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpData, rule10 in *. 
  auto.
Qed.

Lemma rule11_in_DpCtrl: forall (E : set Event) (e1 e2 : Event),
  rule11 E e1 e2 -> DpCtrl E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold DpCtrl, rule11 in *. 
  auto.
Qed.

Lemma rule12_in_M_W_R: forall (E : set Event) (e1 e2 : Event),
  rule12 E e1 e2 -> M_W_R E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_W_R, rule12 in *.
  auto.
Qed.

Lemma rule13_in_M_M_W: forall (E : set Event) (e1 e2 : Event),
  rule13 E e1 e2 -> M_M_W E e1 e2.
Proof.
  intros E e1 e2 H.
  unfold M_M_W, rule13 in *.
  auto.
Qed.
