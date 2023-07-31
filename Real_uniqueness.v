Require Export Real_Axioms.
Section R_Uniqueness.
Variable R1 : Real_struct.
Variable RA1 : Real_axioms R1.
Variable R2 : Real_struct.
Variable RA2 : Real_axioms R2.
Let R' := @R R2.
Let R := @R R1.
Let N' := @N R2.
Let N := @N R1.
Let Z' := @Z R2.
Let Z := @Z R1.
Let Q' := @Q R2.
Let Q := @Q R1.
Let Sup1' := @Sup1 R2.
Let Sup1 := @Sup1 R1.

Declare Scope R1_scope.
Delimit Scope R1_scope with r.
Declare Scope R2_scope.
Delimit Scope R2_scope with r'.
Open Scope R1_scope.

Notation "0" := (@zeroR R1):R1_scope.
Notation "1" := (@oneR R1):R1_scope.
Notation "0 '''" := (@zeroR R2).
Notation "1 '''" := (@oneR R2).
Notation "x + y" := (@fp R1) [[x, y]]:R1_scope.
Notation "x · y" := (@fm R1)[[x, y]]:R1_scope.
Notation "x ≤ y" := ([x, y] ∈ (@Leq R1)):R1_scope.
Notation "- a" := (∩(\{ λ u, u ∈ R /\ u + a = 0 \})):R1_scope.
Notation "x - y" := (x + (-y))%r:R1_scope.
Notation "a ⁻" := (∩(\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \})):R1_scope.
Notation "m / n" := (m · (n⁻))%r:R1_scope.
Notation "x < y" := (@lt R1 x y):R1_scope.
Open Scope R2_scope.
Notation "x + y" := (@fp R2) [[x, y]]:R2_scope.
Notation "x · y" := (@fm R2)[[x, y]]:R2_scope.
Notation "x ≤ y" := ([x, y] ∈ (@Leq R2)):R2_scope.
Notation "- a" := (∩(\{ λ u, u ∈ R' /\ u + a = 0' \})):R2_scope.
Notation "x - y" := (x + (-y)):R2_scope.
Notation "a ⁻" := (∩(\{ λ u, u ∈ (R' ~ [0']) /\ u · a = 1' \})):R2_scope.
Notation "m / n" := (m · (n⁻)):R2_scope.
Notation "x < y" := (@lt R2 x y):R2_scope.
(* 0和1的对应 *)
Hint Resolve PlusR zero_in_R MultR Plus_close Mult_close 
 one_in_R one_in_R_Co Plus_neg1a Plus_neg1b Plus_neg2 Minus_P1 Minus_P2
  Mult_inv1 Mult_inv2 Divide_P1 Divide_P2 OrderPM_Co9 N_Subset_R one_in_N
   Nat_P1a Nat_P1b N_Subset_Z Z_Subset_R Int_P1a Int_P1b Z_Subset_Q 
   Q_Subset_R Rat_P1a Rat_P1b Abs_in_R  : real.
Ltac autoR := match goal with
  | |- 0 ∈ R => apply zero_in_R
  | |- 1 ∈ R => apply one_in_R_Co; autoR
  | |- 1 ∈ N => apply one_in_N; autoR
  | |- 0' ∈ R' => apply zero_in_R
  | |- 1' ∈ R' => apply one_in_R_Co; autoR
  | |- 1' ∈ N' => apply one_in_N; autoR
  | |- (?x + ?y) ∈ R => apply Plus_close; autoR
  | |- _ => eauto with real
  end.

Let PlusMult_Co5' := @PlusMult_Co5 R2 RA2.
Let PlusMult_Co5 := @PlusMult_Co5 R1 RA1.
Let Sup2' := @Sup2 R2.
Let Sup2 := @Sup2 R1.
Let SupT' := @SupT R2 RA2.
Let SupT := @SupT R1 RA1.
Let OrderPM_Co3' := @OrderPM_Co3 R2 RA2.
Let OrderPM_Co3 := @OrderPM_Co3 R1 RA1.
Let OrderPM_Co4' := @OrderPM_Co4 R2 RA2.
Let OrderPM_Co4 := @OrderPM_Co4 R1 RA1.
Let OrderPM_Co7b' := @OrderPM_Co7b R2 RA2.
Let OrderPM_Co7b := @OrderPM_Co7b R1 RA1.
Let Leq_P3' := @Leq_P3 R2 RA2.
Let Leq_P3 := @Leq_P3 R1 RA1.
Let OrderPM_Co7a' := @OrderPM_Co7a R2 RA2.
Let OrderPM_Co7a := @OrderPM_Co7a R1 RA1.
Let Frac_P1' := @Frac_P1 R2 RA2.
Let Frac_P1 := @Frac_P1 R1 RA1.
Let Frac_P2' := @Frac_P2 R2 RA2.
Let Frac_P2 := @Frac_P2 R1 RA1.
Let zero_not_in_N' := @zero_not_in_N R2 RA2.
Let zero_not_in_N := @zero_not_in_N R1 RA1.
Let Mult_P3' := @Mult_P3 R2 RA2.
Let Mult_P3 := @Mult_P3 R1 RA1.
Let Nat_P4' := @Nat_P4 R2 RA2.
Let Nat_P4 := @Nat_P4 R1 RA1.
Let Nat_P2' := @Nat_P2 R2 RA2.
Let Nat_P2 := @Nat_P2 R1 RA1.
Let Mult_P5' := @Mult_P5 R2 RA2.
Let Mult_P5 := @Mult_P5 R1 RA1.
Let Nat_P7' := @Nat_P7 R2 RA2.
Let Nat_P7 := @Nat_P7 R1 RA1.
Let Arch_P3a' := @Arch_P3a R2 RA2.
Let Arch_P3a := @Arch_P3a R1 RA1.
Let Arch_P2' := @Arch_P2 R2 RA2.
Let Arch_P2 := @Arch_P2 R1 RA1.
Let Upper' := @Upper R2.
Let Upper := @Upper R1.
Let Arch_P10' := @Arch_P10 R2 RA2.
Let Arch_P10 := @Arch_P10 R1 RA1.
Let Sup_Corollary' := @Sup_Corollary R2 RA2.
Let Sup_Corollary := @Sup_Corollary R1 RA1.
Let Min_Corollary' := @Min_Corollary R2 RA2.
Let Min_Corollary := @Min_Corollary R1 RA1.
Let Arch_P9' := @Arch_P9 R2 RA2.
Let Arch_P9 := @Arch_P9 R1 RA1.
Let Order_Co1' := @Order_Co1 R2 RA2.
Let Order_Co1 := @Order_Co1 R1 RA1.
Let Mult_P1' := @Mult_P1 R2 RA2.
Let Mult_P1 := @Mult_P1 R1 RA1.
Let OrderPM_Co5' := @OrderPM_Co5 R2 RA2.
Let OrderPM_Co5 := @OrderPM_Co5 R1 RA1.
Let OrderPM_Co10' := @OrderPM_Co10 R2 RA2.
Let OrderPM_Co10 := @OrderPM_Co10 R1 RA1.
Let Plus_Co3' := @Plus_Co3 R2 RA2.
Let Plus_Co3 := @Plus_Co3 R1 RA1.
Let PlusMult_Co1' := @PlusMult_Co1 R2 RA2.
Let PlusMult_Co1 := @PlusMult_Co1 R1 RA1.
Let Mult_Co3' := @Mult_Co3 R2 RA2.
Let Mult_Co3 := @Mult_Co3 R1 RA1.
Let Plus_P4' := @Plus_P4 R2 RA2.
Let Plus_P4 := @Plus_P4 R1 RA1.
Let Plus_P1' := @Plus_P1 R2 RA2.
Let Plus_P1 := @Plus_P1 R1 RA1.
Let PlusMult_Co3' := @PlusMult_Co3 R2 RA2.
Let PlusMult_Co3 := @PlusMult_Co3 R1 RA1.
Let Mult_P4' := @Mult_P4 R2 RA2.
Let Mult_P4 := @Mult_P4 R1 RA1.
Let one_is_min_in_N' := @one_is_min_in_N R2 RA2.
Let one_is_min_in_N := @one_is_min_in_N R1 RA1.
Let Order_Co2' := @Order_Co2 R2 RA2.
Let Order_Co2 := @Order_Co2 R1 RA1.
Let OrderPM_Co2a' := @OrderPM_Co2a R2 RA2.
Let OrderPM_Co2a := @OrderPM_Co2a R1 RA1.
Let Leq_P2' := @Leq_P2 R2 RA2.
Let Leq_P2 := @Leq_P2 R1 RA1.
Let MathInd' := @MathInd R2 RA2.
Let MathInd := @MathInd R1 RA1.
Let PlusMult_Co4' := @PlusMult_Co4 R2 RA2.
Let PlusMult_Co4 := @PlusMult_Co4 R1 RA1.
Let Int_P3' := @Int_P3 R2 RA2.
Let Int_P3 := @Int_P3 R1 RA1.
Let Leq_P1' := @Leq_P1 R2 RA2.
Let Leq_P1 := @Leq_P1 R1 RA1.
Let OrderPM_Co1' := @OrderPM_Co1 R2 RA2.
Let OrderPM_Co1 := @OrderPM_Co1 R1 RA1.
Let Plus_P3' := @Plus_P3 R2 RA2.
Let Plus_P3 := @Plus_P3 R1 RA1.

Let Plus_close' := @Plus_close R2 RA2.
Let zero_in_R' := @zero_in_R R2 RA2.
Let Mult_close' := @Mult_close R2 RA2.
Let one_in_R' := @one_in_R R2 RA2.
Let one_in_R_Co' := @one_in_R_Co R2 RA2.
Let Plus_neg1a' := @Plus_neg1a R2 RA2.
Let Plus_neg1b' := @Plus_neg1b R2 RA2.
Let Plus_neg2' := @Plus_neg2 R2 RA2.
Let Minus_P1' := @Minus_P1 R2 RA2.
Let Minus_P2' := @Minus_P2 R2 RA2.
Let Mult_inv1' := @Mult_inv1 R2 RA2.
Let Mult_inv2' := @Mult_inv2 R2 RA2.
Let Divide_P1' := @Divide_P1 R2 RA2.
Let Divide_P2' := @Divide_P2 R2 RA2.
Let OrderPM_Co9' := @OrderPM_Co9 R2 RA2.
Let N_Subset_R' := @N_Subset_R R2 RA2.
Let one_in_N' := @one_in_N R2 RA2.
Let Nat_P1a' := @Nat_P1a R2 RA2.
Let Nat_P1b' := @Nat_P1b R2 RA2.
Let N_Subset_Z' := @N_Subset_Z R2.
Let Z_Subset_R' := @Z_Subset_R R2 RA2.
Let Int_P1a' := @Int_P1a R2 RA2.
Let Int_P1b' := @Int_P1b R2 RA2.
Let Z_Subset_Q' := @Z_Subset_Q R2 RA2.
Let Q_Subset_R' := @Q_Subset_R R2 RA2.
Let Rat_P1a' := @Rat_P1a R2 RA2.
Let Rat_P1b' := @Rat_P1b R2 RA2.
Let Abs_in_R' := @Abs_in_R R2 RA2.

Let Plus_close := @Plus_close R1 RA1.
Let zero_in_R := @zero_in_R R1 RA1.
Let Mult_close := @Mult_close R1 RA1.
Let one_in_R := @one_in_R R1 RA1.
Let one_in_R_Co := @one_in_R_Co R1 RA1.
Let Plus_neg1a := @Plus_neg1a R1 RA1.
Let Plus_neg1b := @Plus_neg1b R1 RA1.
Let Plus_neg2 := @Plus_neg2 R1 RA1.
Let Minus_P1 := @Minus_P1 R1 RA1.
Let Minus_P2 := @Minus_P2 R1 RA1.
Let Mult_inv1 := @Mult_inv1 R1 RA1.
Let Mult_inv2 := @Mult_inv2 R1 RA1.
Let Divide_P1 := @Divide_P1 R1 RA1.
Let Divide_P2 := @Divide_P2 R1 RA1.
Let OrderPM_Co9 := @OrderPM_Co9 R1 RA1.
Let N_Subset_R := @N_Subset_R R1 RA1.
Let one_in_N := @one_in_N R1 RA1.
Let Nat_P1a := @Nat_P1a R1 RA1.
Let Nat_P1b := @Nat_P1b R1 RA1.
Let N_Subset_Z := @N_Subset_Z R1.
Let Z_Subset_R := @Z_Subset_R R1 RA1.
Let Int_P1a := @Int_P1a R1 RA1.
Let Int_P1b := @Int_P1b R1 RA1.
Let Z_Subset_Q := @Z_Subset_Q R1 RA1.
Let Q_Subset_R := @Q_Subset_R R1 RA1.
Let Rat_P1a := @Rat_P1a R1 RA1.
Let Rat_P1b := @Rat_P1b R1 RA1.
Let Abs_in_R := @Abs_in_R R1 RA1.

Hint Resolve 
Plus_close zero_in_R Mult_close one_in_R one_in_R_Co
Plus_neg1a Plus_neg1b Plus_neg2 Minus_P1 Minus_P2
Mult_inv1 Mult_inv2 Divide_P1 Divide_P2 OrderPM_Co9
N_Subset_R one_in_N Nat_P1a Nat_P1b
N_Subset_Z Z_Subset_R Int_P1a Int_P1b
Z_Subset_Q Q_Subset_R Rat_P1a Rat_P1b Abs_in_R : real.

Hint Resolve 
Plus_close' zero_in_R' Mult_close' one_in_R' one_in_R_Co'
Plus_neg1a' Plus_neg1b' Plus_neg2' Minus_P1' Minus_P2'
Mult_inv1' Mult_inv2' Divide_P1' Divide_P2' OrderPM_Co9'
N_Subset_R' one_in_N' Nat_P1a' Nat_P1b'
N_Subset_Z' Z_Subset_R' Int_P1a' Int_P1b'
Z_Subset_Q' Q_Subset_R' Rat_P1a' Rat_P1b' Abs_in_R' : real'.

(* 0和1的对应 *)
Theorem UniqueT1 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r')
  -> f[0] = 0' /\ (ran(f) <> [0'] -> f[1] = 1')).
Proof.
  assert (H:True) by auto.
  intros. assert (f[0] ∈ R' /\ f[1] ∈ R') as [].
  { split; apply H2; [apply (@ Property_ran 0)|
    apply (@ Property_ran 1)]; apply Property_Value; auto;
    rewrite H1; auto with real. }
  pose proof zero_in_R. apply (H3 0 0) in H6 as []; auto with real.
  assert (f[(0 + 0)%r] = f[0]). { rewrite Plus_P1; auto with real. }
  rewrite H6 in H8. apply Plus_Co3' in H8; auto.
  rewrite Minus_P1' in H8; auto. split; auto. intros.
  pose proof one_in_R_Co. apply (H3 1 1) in H10 as []; auto with real.
  assert (f[(1 · 1)%r] = f[1]). { rewrite Mult_P1; auto with real. }
  rewrite H12 in H11. symmetry in H11.
  assert (f[1] ∈ (R' ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H13; eauto with real'. elim H9.
    apply AxiomI; split; intros. apply Einr in H14 as [x[]]; auto.
    pose proof H14. rewrite H1 in H14,H16.
    apply (H3 x 1) in H16 as []; auto with real.
    rewrite Mult_P1,H13,PlusMult_Co1' in H17; auto.
    apply MKT41; eauto with real'. rewrite H15; auto.
    rewrite <-H1 in H14. apply Property_Value,Property_ran in H14;
    auto. apply MKT41 in H14; eauto with real'. rewrite H14.
    assert (0∈dom( f)). rewrite H1. auto with real.
    apply Property_Value,Property_ran in H15; auto.
    rewrite H8 in H15; auto. }
  apply Mult_Co3' in H11; auto. rewrite Divide_P1' in H11; auto.
Qed.

(* 整数集的对应 *)
Lemma UniqueT2_Lemma1 :
  (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ m, m ∈ N -> f[m] ∈ N')).
Proof.
  assert (H:True) by auto.
  intros. set (E := \{ λ u, u ∈ N /\ f[u] ∈ N' \}).
  assert (E ⊂ N /\ 1 ∈ E) as [].
  { split. unfold Included; intros. apply AxiomII in H6; tauto.
    apply AxiomII; repeat split; eauto with real.
    apply UniqueT1 in H4; auto. rewrite H4; auto with real'. }
  assert (E = N).
  { apply MathInd; auto. intros. apply AxiomII; repeat split;
    eauto with real. pose proof H8.
    apply H6,N_Subset_R,(H3 x 1) in H9 as []; auto with real.
    rewrite H9. apply UniqueT1 in H4; auto. rewrite H4.
    apply Nat_P1a'; auto with real'. apply AxiomII in H8; tauto. }
  rewrite <-H8 in H5. apply AxiomII in H5; tauto.
Qed.

Lemma UniqueT2_Lemma2 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> f[(-(1))%r] = -f[1]).
Proof.
  assert (H:True) by auto.
  intros. pose proof one_in_R_Co.
  apply (H3 1 (-(1))%r) in H5 as []; auto with real.
  rewrite Minus_P1 in H5; auto with real.
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  symmetry in H5. apply Plus_Co3' in H5; auto with real.
  apply UniqueT1 in H0 as []; auto. rewrite H0 in H5.
  rewrite Plus_P4',Plus_P1' in H5; auto with real' real.
Qed.

Lemma UniqueT2_Lemma3 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ r, r ∈ R -> f[(-r)%r] = -f[r])).
Proof.
  assert (H:True) by auto.
  intros. pose proof one_in_R_Co. apply Plus_neg1a in H6.
  apply (H3 r) in H6 as []; auto with real.
  rewrite UniqueT2_Lemma2 in H7; auto. pose proof H0.
  apply UniqueT1 in H8 as []; auto. rewrite H9 in H7; auto.
  rewrite Mult_P4,<-PlusMult_Co3 in H7; auto with real.
  assert (f[r] ∈ R').
  { rewrite <-H1 in H5.
    apply Property_Value,Property_ran in H5; auto. }
  rewrite PlusMult_Co3',Mult_P4'; auto with real'.
Qed.

Lemma UniqueT2_Lemma4 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ m, m ∈ R -> m <> 0 -> f[m] <> 0')).
Proof.
  assert (H:True) by auto.
  intros. intro. elim H4. apply AxiomI; split; intros.
  apply Einr in H8 as [x[]]; auto.
  assert (m ∈ (R ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H10; eauto with real. }
  replace x with (m · (x / m))%r in H9. pose proof H8.
  rewrite H1 in H11. pose proof H10. apply Mult_inv1,MKT4' in H12
  as [H12 _]. pose proof H5. apply (H3 m (x / m)%r) in H13 as [];
  auto with real. assert (f[(x / m)%r] ∈ R').
  { apply H2,(@ Property_ran (x / m)%r),Property_Value; auto.
    rewrite H1; auto with real. }
  rewrite H14,H7,Mult_P4',PlusMult_Co1' in H9; auto with real'.
  apply MKT41; eauto with real'. rewrite H1 in H8. pose proof H10.
  apply Mult_inv1,MKT4' in H10 as []. rewrite Mult_P3,(Mult_P4 m),
  <-Mult_P3,Divide_P1,Mult_P1; auto with real.
  apply MKT41 in H8; eauto with real'. rewrite H8.
  rewrite <-H7. apply (@ Property_ran m),Property_Value; auto.
  rewrite H1; auto.
Qed.

Lemma UniqueT2_Lemma5 : ∀ n, n ∈ Z -> (0 < n)%r -> n ∈ N.
Proof.
  intros. apply MKT4 in H as []; auto.
  apply MKT4 in H as []. apply AxiomII in H as [].
  assert (0 < -n)%r.
  { destruct one_is_min_in_N as [_[]].
    apply (Order_Co2 _ 1); auto with real. }
  apply OrderPM_Co2a in H0; auto with real.
  destruct H0,H2. elim H4. apply Leq_P2; auto with real.
  apply MKT41 in H; eauto with real. rewrite H in H0.
  destruct H0. elim H1; auto.
Qed.

Theorem UniqueT2 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r')
  -> ran(f) <> [0'] -> (∀ m, m ∈ Z -> f[m] ∈ Z')
    /\ Function1_1 (f|(Z)) /\ dom(f|(Z)) = Z /\ ran(f|(Z)) = Z'
    /\ (∀ x y, x ∈ Z -> y ∈ Z -> (x ≤ y)%r -> (f[x] ≤ f[y])%r')).
Proof.
  assert (H:True) by auto.
  intros. pose proof H0. apply UniqueT1 in H5 as []; auto.
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert (∀ m, m ∈ Z -> f[m] ∈ Z').
  { intros. apply MKT4 in H8 as [].
    apply N_Subset_Z',UniqueT2_Lemma1; auto.
    apply MKT4 in H8 as []. apply AxiomII in H8 as [].
    assert (f[(-m)%r] ∈ N'). { apply UniqueT2_Lemma1; auto. }
    pose proof H0. apply UniqueT2_Lemma2 in H11; auto.
    rewrite PlusMult_Co3 in H10; auto with real.
    pose proof H9. apply N_Subset_R,Plus_neg1b in H12.
    apply (H3 (-(1))%r m) in H12 as []; auto. (* [ |apply Plus_neg1a]; *)
    auto with real. assert ((@Real_Axioms.R R1) = R). auto. rewrite H14 in H10.
    rewrite H13 ,H11,H6,<-PlusMult_Co3' in H10;
    auto with real. apply MKT4; right. apply MKT4; left.
    apply AxiomII; split; auto. exists R'. auto with real.
    apply MKT41 in H8; eauto with real. rewrite H8,H5.
    repeat (apply MKT4; right). apply MKT41; eauto with real'. }
  assert (Function1_1 (f|(Z))).
  { split. apply MKT126a; auto. split; unfold Relation; intros.
    - apply AxiomII in H9 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H9 as [_],H10 as [_].
      apply MKT4' in H9 as [],H10 as [].
      apply AxiomII' in H11 as [_[H11 _]],H12 as [_[H12 _]].
      pose proof H9. apply Property_ran,H2 in H13.
      apply Property_Fun in H9,H10; auto.
      assert (f[y] + f[(-z)%r] = 0').
      { pose proof H0. apply UniqueT2_Lemma2 in H14; auto.
        pose proof H12. apply Z_Subset_R in H15.
        apply (H3 (-(1))%r z) in H15 as []; auto with real.
        assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
        rewrite PlusMult_Co3. rewrite ReqR. rewrite H16, H14,H6,<-PlusMult_Co3',
        <-H9,<-H10,Minus_P1'; auto with real. rewrite ReqR; autoR. }
      pose proof H11. apply Z_Subset_R,(H3 y (-z)%r) in H15 as [];
      auto with real. rewrite <-H15 in H14. apply NNPP; intro.
      assert (y - z <> 0)%r.
      { intro. assert (y - z + z = 0 + z)%r. { rewrite H18; auto. }
        rewrite <-Plus_P3,(Plus_P4 _ z),Minus_P1,(Plus_P4 0),
        Plus_P1,Plus_P1 in H19; auto with real. }
      assert (f[(y - z)%r] <> 0'); auto.
      { apply UniqueT2_Lemma4; auto with real. } }
  assert (dom(f|(Z)) = Z).
  { rewrite MKT126b; auto. apply MKT30.
    rewrite H1; auto with real. }
  assert (∀ n, n ∈ N' -> n ∈ ran(f|(Z))).
  { set (E := \{ λ u, u ∈ N' /\ u ∈ ran(f|(Z)) \}). destruct H9.
    assert (E ⊂ N' /\ 1' ∈ E) as [].
    { split. unfold Included; intros. apply AxiomII in H12;
      tauto. apply AxiomII; repeat split; eauto with real'.
      rewrite <-H6,<-(MKT126c f Z); auto;
      [ |rewrite H10; auto with real]. apply (@ Property_ran 1),
      Property_Value; auto. rewrite H10. auto with real. }
    assert (E = N').
    { apply MathInd'; auto. intros. apply AxiomII in H13
      as [_[]]. apply AxiomII; repeat split; eauto with real'.
      apply AxiomII in H14 as [_[]]. pose proof H15.
      pose proof H16. rewrite reqdi in H17,H18.
      apply Property_Value,Property_ran in H17,H18; auto.
      rewrite <-deqri in H17,H18.
      assert (f[(((f|(Z))⁻¹)[x] + ((f|(Z))⁻¹)[1'])%r] = x + 1').
      { rewrite H10 in H17,H18. pose proof H17.
        apply Z_Subset_R,(H3 (((f|(Z))⁻¹)[x])) in H19
        as [H19 _]; auto with real.
        rewrite <-(MKT126c f Z),<-(MKT126c f Z),<-(MKT126c f Z),
        MKT126c in H19; try rewrite H10; auto with real.
        rewrite f11vi,f11vi in H19; auto. }
      rewrite H10 in H17,H18. rewrite <-H19,<-(MKT126c f Z);
      try rewrite H10; auto with real.
      apply (@ Property_ran (((f|(Z))⁻¹)[x]
        + ((f|(Z))⁻¹)[1'])%r),Property_Value;
      try rewrite H10; auto with real. }
    intros. rewrite <-H14 in H15. apply AxiomII in H15; tauto. }
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (ran(f|(Z)) = Z').
  { destruct H9. apply AxiomI; split; intros.
    apply Einr in H13 as [x[]]; auto. rewrite MKT126c in H14; auto.
    rewrite H10 in H13. rewrite H14; auto.
    apply MKT4 in H13 as []; auto. apply MKT4 in H13 as [].
    apply AxiomII in H13 as []. pose proof H14. apply H11 in H15.
    rewrite reqdi in H15. apply Property_Value,Property_ran
    in H15; auto. rewrite <-deqri in H15.
    assert (f[(((f|(Z))⁻¹)[(-z)%r'] · (-(1)))%r] = -z · -1').
    { rewrite H10 in H15. pose proof H15.
      apply Z_Subset_R,(H3 _ (-(1))%r) in H16 as [_];
      auto with real. pose proof H0. apply UniqueT2_Lemma2
      in H17; auto. rewrite ReqR, ReqR' in *.
      rewrite <-(MKT126c f Z H0 (((f|(Z))⁻¹)[-z])),
      f11vi,H17,H6 in H16; auto. rewrite H10; auto. }
    rewrite ReqR, ReqR' in *.
    rewrite (Mult_P4' (-z)),PlusMult_Co4' in H16;
    auto with real'. rewrite <-H16. rewrite H10 in H15.
    rewrite <-(MKT126c f Z); auto; [ |rewrite H10;
    apply Int_P1b; auto; apply Int_P3; auto with real].
    apply (@ Property_ran (((f|(Z))⁻¹)[(-z)%r'] · -(1))%r),
    Property_Value; auto. rewrite H10. apply Int_P1b; auto.
    apply Int_P3. auto with real. apply MKT41 in H13;
    eauto with real'. assert (0 ∈ dom(f|(Z))).
    { rewrite H10. repeat (apply MKT4; right).
      apply MKT41; eauto with real. }
    rewrite H13,<-H5,<-(MKT126c f Z); auto.
    apply (@ Property_ran 0),Property_Value; auto. }
  split; [ |split; [ |repeat split]]; auto. intros.
  destruct (classic (x = y)). rewrite H16.
  apply Leq_P1'; auto with real'.
  assert ((y - x)%r ∈ N).
  { apply UniqueT2_Lemma5. apply Int_P1a; auto.
    apply Int_P3; auto. assert (x < y)%r. { split; auto. }
    apply (OrderPM_Co1 _ _ (-x)%r) in H17; auto with real.
    rewrite Minus_P1 in H17; auto with real. }
  assert (f[(y - x)%r] ∈ N'). { apply UniqueT2_Lemma1; auto. }
  pose proof H14. apply Z_Subset_R,(H3 y (-x)%r) in H19
  as [H19 _]; auto. rewrite UniqueT2_Lemma3 in H19; auto with real.
  rewrite H19 in H18. assert (0' < (f[y] - f[x])).
  { destruct one_is_min_in_N' as [_[]].
    apply (Order_Co2' _ 1'); auto with real'. }
  apply (OrderPM_Co1' _ _ f[x]) in H20; auto with real'.
  rewrite Plus_P4',Plus_P1',<-Plus_P3',(Plus_P4' (-f[x])),
  Minus_P1',Plus_P1' in H20; auto with real'. destruct H20; auto.
Qed.

Lemma UniqueT3_Lemma1 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ r, r ∈ (R ~ [0]) -> f[(r⁻)%r] = ((f[r])⁻)%r')).
Proof.
  assert (H:True) by auto.
  intros. pose proof H5. apply Mult_inv1,MKT4' in H6 as [H6 _].
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  pose proof H5. apply MKT4' in H8 as []. apply AxiomII in H9 as [_].
  assert (f[r] ∈ (R' ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. elim H9. apply MKT41. eauto with real.
    apply NNPP; intro. apply MKT41 in H10; eauto with real'.
    apply NNPP in H10. apply H10,UniqueT2_Lemma4; auto. }
  assert (f[r] · f[(r⁻)%r] = 1').
  { pose proof H8. apply (H3 _ (r⁻)%r) in H11 as [_]; auto.
    apply UniqueT1 in H0 as []; auto.
    rewrite Divide_P1,H12 in H11; auto. }
  apply Mult_Co3' in H11; auto with real'.
  apply Mult_inv1',MKT4' in H10 as [].
  rewrite Mult_P4',Mult_P1' in H11; auto with real'.
Qed.

Lemma UniqueT3_Lemma2 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ r, r ∈ Q -> (0 < r)%r -> (0' < f[r])%r')).
Proof.
  assert (H:True) by auto.
  intros. apply Existence_of_irRational_Number_Lemma6 in H6
  as [a[b[H6[]]]]; auto. assert (b ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII;
    split; eauto. intro. apply MKT41 in H9; eauto with real.
    destruct one_is_min_in_N as [_[_]]. pose proof H7.
    apply H10 in H11. rewrite H9 in H11.
    assert (0 < 0)%r as []; auto.
    { apply (Order_Co2 _ 1); auto with real. } }
  pose proof H9. apply Mult_inv1,MKT4' in H10 as [H10 _].
  apply (H3 a) in H10 as [_]; auto with real.
  rewrite UniqueT3_Lemma1 in H10; auto.
  assert (f[a] ∈ N' /\ f[b] ∈ N') as [].
  { split; apply UniqueT2_Lemma1; auto. }
  assert (0' < f[a] /\ 0' < f[b]) as [].
  { destruct one_is_min_in_N' as [_[_]].
    split; apply (Order_Co2' _ 1'); auto with real'. }
  assert (f[b] ∈ (R' ~ [0'])).
  { apply MKT4'; split; auto with real'. apply AxiomII;
    split; eauto. intro. apply MKT41 in H15; eauto with real'.
    rewrite H15 in H14. destruct H14; auto. }
  apply Mult_inv1',MKT4' in H15 as [H15 _].
  rewrite H8,H10. apply OrderPM_Co5'; auto with real'.
Qed.

(* 有理数集的对应 *)
Theorem UniqueT3 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ m n, m ∈ Z -> n ∈ (Z ~ [0]) -> f[(m/n)%r] = (f[m] / f[n])%r')
    /\ Function1_1 (f|(Q)) /\ dom(f|(Q)) = Q /\ ran(f|(Q)) = Q'
    /\ (∀ x y, x ∈ Q -> y ∈ Q -> (x ≤ y)%r -> (f[x] ≤ f[y])%r')).
Proof.
  assert (H:True) by auto.
  intros. pose proof H0. apply UniqueT1 in H5 as []; auto.
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert (∀ m, m ∈ Z -> f[m] ∈ Z'). { apply UniqueT2; auto. }
  assert (∀ m, m ∈ (Z ~ [0]) -> f[m] ∈ (Z' ~ [0'])) as H8'.
  { intros. apply MKT4' in H9 as []. apply MKT4'; split; auto.
    apply AxiomII; split; eauto. intro. apply AxiomII in H10 as [_].
    apply H10,MKT41; eauto with real. apply NNPP; intro.
    apply MKT41 in H11; eauto with real'. apply NNPP in H11.
    apply H11,UniqueT2_Lemma4; auto with real. }
  assert (∀ m n, m ∈ Z -> n ∈ (Z ~ [0])
    -> f[(m / n)%r] = f[m] / f[n]).
  { intros. assert (m ∈ R /\ n ∈ (R ~ [0])) as [].
    { apply MKT4' in H10 as [].
      split; [ |apply MKT4'; split]; auto with real. }
    pose proof H11. apply (H3 _ (n⁻)%r) in H13 as [_]; auto.
    rewrite UniqueT3_Lemma1 in H13; auto.
    apply Mult_inv1,MKT4' in H12 as []; auto. }
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (Function1_1 (f|(Q))) as [].
  { split. apply MKT126a; auto. split; unfold Relation; intros.
    - apply AxiomII in H10 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H10 as [_],H11 as [_].
      apply MKT4' in H10 as [],H11 as [].
      apply AxiomII' in H12 as [_[H12 _]],H13 as [_[H13 _]].
      pose proof H10. apply Property_ran,H2 in H14.
      apply Property_Fun in H10,H11; auto.
      assert (f[y] + f[(-z)%r] = 0').
      { pose proof H0. apply UniqueT2_Lemma2 in H15; auto.
        pose proof H13. apply Q_Subset_R in H16.
        apply (H3 (-(1))%r z) in H16 as []; auto with real.
        rewrite PlusMult_Co3. rewrite ReqR, ReqR' in *.
        rewrite H17, H15,H6,<-PlusMult_Co3',
        <-H10,<-H11,Minus_P1'; auto with real. rewrite ReqR; autoR. }
      pose proof H12. apply Q_Subset_R,(H3 y (-z)%r) in H16 as [];
      auto with real. rewrite <-H16 in H15. apply NNPP; intro.
      assert (y - z <> 0)%r.
      { intro. assert (y - z + z = 0 + z)%r. { rewrite H19; auto. }
        rewrite <-Plus_P3,(Plus_P4 _ z),Minus_P1,(Plus_P4 0),
        Plus_P1,Plus_P1 in H20; auto with real. }
      assert (f[(y - z)%r] <> 0'); auto.
      { apply UniqueT2_Lemma4; auto with real. } }
  assert (dom(f|(Q)) = Q).
  { rewrite MKT126b; auto. apply MKT30.
    rewrite H1; auto with real. }
  pose proof H0. apply UniqueT2 in H13 as [H13[[][H16[]]]]; auto.
  assert (ZeqZ:@Real_Axioms.Z R1 = Z) by auto.
  assert (ZeqZ':@Real_Axioms.Z R2 = Z') by auto.
  assert (ran(f|(Q)) = Q').
  { apply AxiomI; split; intros. apply Einr in H19 as [x[]]; auto.
    rewrite MKT126c in H20; auto. rewrite H12 in H19. pose proof H19.
    apply AxiomII in H21 as [H21[m[n[H22[]]]]]. pose proof H20.
    rewrite H24,H9 in H20; auto. rewrite H20. apply AxiomII; split.
    rewrite <-H20,H25. eauto with real. exists f[m],f[n]; auto.
    pose proof H19. apply AxiomII in H20 as [_[m[n[H21[]]]]].
    pose proof H20; pose proof H21. apply MKT4' in H23 as [H23 _].
    rewrite ZeqZ' in *.
    rewrite <-H17, reqdi in H23,H24. apply Property_Value,Property_ran
    in H23,H24; auto. rewrite <-deqri in H23,H24.
    assert (((f|(Z))⁻¹)[n] ∈ (Z ~ [0])).
    { apply MKT4'; split. rewrite H16 in H23; auto.
      apply AxiomII; split; eauto. intro. apply MKT41 in H25;
      eauto with real. apply MKT4' in H20 as [].
      rewrite <-H25,<-(MKT126c f Z),f11vi in H5; auto.
      rewrite <-H5 in H26. apply AxiomII in H26 as [].
      apply H27,MKT41; eauto. rewrite H17; auto. }
    pose proof H24. rewrite H16 in H26.
    apply (H9 _ (((f|(Z))⁻¹)[n])) in H26; auto.
    rewrite <-(MKT126c f Z H0 (((f|(Z))⁻¹)[m])),
    <-(MKT126c f Z H0 (((f|(Z))⁻¹)[n])),f11vi,f11vi in H26;
    try rewrite H17; auto; [ |apply MKT4' in H20; tauto].
    assert ((((f|(Z))⁻¹)[m] / ((f|(Z))⁻¹)[n])%r ∈ dom(f|(Q))).
    { rewrite H12. rewrite H16 in H24. apply AxiomII; split; eauto.
      exists R. apply Mult_close; auto with real.
      assert (((f|(Z))⁻¹)[n] ∈ (R ~ [0])).
      { apply MKT4' in H25 as [].
        apply MKT4'; split; auto with real. }
      apply Mult_inv1,MKT4' in H27 as []; auto. }
    rewrite <-(MKT126c f Q) in H26; auto.
    apply Property_Value,Property_ran in H27; auto.
    rewrite ReqR, ReqR' in *.
    rewrite H26,<-H22 in H27; auto. }
  split; [ |split; [split|repeat split]]; auto. intros.
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H23.
    apply Property_Value,Property_ran in H23; auto. }
  destruct (classic (x = y)). rewrite H24.
  apply Leq_P1'; auto with real real'.
  assert (x < y)%r. split; auto.
  apply (OrderPM_Co1 _ _ (-x)%r) in H25; auto with real.
  rewrite Minus_P1 in H25; auto with real.
  assert ((y - x)%r ∈ Q).
  { apply Rat_P1a; auto. apply Rat_P3; auto. }
  assert (0' < (f[(y - x)%r])). { apply UniqueT3_Lemma2; auto. }
  pose proof H21. apply Q_Subset_R in H28.
  apply (H3 y (-x)%r) in H28 as [H28 _]; auto with real.
  rewrite UniqueT2_Lemma3 in H28; auto with real.
  rewrite H28 in H27. apply Q_Subset_R,H23 in H20,H21.
  apply (OrderPM_Co1' _ _ f[x]) in H27; auto with real'.
  rewrite Plus_P4',Plus_P1',<-Plus_P3',(Plus_P4' _ f[x]),
  Minus_P1',Plus_P1' in H27; auto with real'. destruct H27; auto.
Qed.

Lemma UniqueT4_Lemma1 : ∀ r, r ∈ R'
  -> Sup1' \{ λ u, u ∈ Q' /\ u ≤ r \} r.
Proof.
  intros. repeat split; intros; auto. unfold Included; intros.
  apply AxiomII in H0 as [_[]]; auto with real'.
  apply AxiomII in H0; tauto. apply Arch_P9' in H1 as [q[H1[H2[]]]];
  auto. exists q. split; auto. apply AxiomII; split; eauto.
Qed.

Lemma UniqueT4_Lemma2 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ x y, x ∈ R -> y ∈ R -> (x < y)%r <-> (f[x] < f[y])%r')).
Proof.
  assert (H:True) by auto. intros.
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (∀ r, r ∈ R -> (0 < r)%r -> 0' < f[r]).
  { intros. apply Existence_of_irRational_Number_Lemma5 in H8
    as [e[H8[]]]; auto. pose proof H8. apply (H3 e e) in H11
    as []; auto. pose proof H8. rewrite ReqR, ReqR' in *.
    rewrite <-H1 in H13.
    apply Property_Value,Property_ran,H2 in H13; auto.
    rewrite <-H10,H12. apply OrderPM_Co5'; auto.
    pose proof H13. apply (Order_Co1' 0') in H14 as [H14|[]];
    auto with real'.
    assert (∀ r, r ∈ R -> r <> 0 -> f[r] <> 0').
    { apply UniqueT2_Lemma4; auto. }
    destruct H9. apply H15 in H8; auto. elim H8; auto. }
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H8.
    apply Property_Value,Property_ran in H8; auto. }
  assert (∀ a b, a ∈ R -> b ∈ R -> (a < b)%r -> f[a] < f[b]).
  { intros. apply (OrderPM_Co1 _ _ (-a)%r) in H11; auto with real.
    rewrite Minus_P1 in H11; auto. apply H7 in H11; auto with real.
    pose proof H10. apply (H3 b (-a)%r) in H12 as []; auto with real.
    rewrite H12,UniqueT2_Lemma3 in H11; auto.
    apply (OrderPM_Co1' _ _ f[a]) in H11; auto with real'.
    rewrite Plus_P4',Plus_P1',<-Plus_P3',(Plus_P4' _ f[a]),
    Minus_P1',Plus_P1' in H11; auto with real'. }
  split; auto. intros. pose proof H5.
  apply (Order_Co1 x y) in H11 as [H11|[]]; auto.
  apply H9 in H11; auto. destruct H10,H11. elim H13.
  apply Leq_P2'; auto with real'. rewrite H11 in H10.
  destruct H10. elim H12; auto.
Qed.

Lemma UniqueT4_Lemma3 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> (∀ A r, A ⊂ Q -> r ∈ R -> Sup1 A r -> Sup1' ran(f|(A)) f[r])).
Proof.
  assert (H:True) by auto. intros. 
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (QeqQ: (@Real_Axioms.Q R1) = Q) by auto.
  assert (QeqQ': (@Real_Axioms.Q R2) = Q') by auto.
  destruct H7 as [[H7[_]]].
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H10.
    apply Property_Value,Property_ran in H10; auto. }
  assert (∀ x y, x ∈ R -> y ∈ R -> (x ≤ y)%r -> (f[x] ≤ f[y])%r').
  { intros. destruct (classic (x = y)). rewrite H14.
    apply Leq_P1'; auto. assert (x < y)%r. split; auto.
    apply UniqueT4_Lemma2; auto. }
  assert (Function (f|(A))). { apply MKT126a; auto. }
  repeat split; auto; unfold Included; intros.
  apply AxiomII in H13 as [H13[]]. apply MKT4' in H14 as [].
  apply Property_ran in H14; auto. apply AxiomII in H13 as [_[]].
  apply MKT4' in H13 as []. apply AxiomII' in H14 as [_[]].
  apply Property_Fun in H13; auto. rewrite H13.
  apply H11; auto with real. apply Arch_P9' in H14 as [q[H14[]]];
  auto. assert (q ∈ ran(f)).
  { pose proof H0. apply UniqueT3 in H17 as [H17[[][H20[]]]]; auto.
    rewrite QeqQ, QeqQ' in *.
    rewrite <-H21 in H14. apply Einr in H14 as [x[]]; auto.
    rewrite MKT126c in H23; auto. rewrite H20 in H14.
    apply Q_Subset_R in H14. rewrite ReqR, ReqR' in *. rewrite <-H1 in H14.
    apply Property_Value,Property_ran in H14; auto.
    rewrite H23; auto. }
  apply Einr in H17 as [x[]]; auto.
  assert (x < r)%r.
  { rewrite H1 in H17. rewrite H18 in H16. pose proof H17.
    apply (Order_Co1 r) in H19 as [H19|[]]; auto. destruct H19.
    apply H11 in H19; auto. destruct H16. elim H21.
    apply Leq_P2'; auto. rewrite H19 in H16. destruct H16.
    elim H20; auto. }
  rewrite H1 in H17. apply H9 in H19 as [x0[]]; auto.
  assert (x0 ∈ dom(f|(A))).
  { rewrite MKT126b; auto. apply MKT30 in H7. rewrite ReqR, ReqR' in *.
   rewrite H1,H7; auto. }
  exists f[x0]. split. rewrite <-(MKT126c f A); auto.
  apply (@ Property_ran x0),Property_Value; auto.
  apply (Order_Co2' _ q); auto with real'. left. split; auto.
  rewrite H18. apply H11; auto. destruct H20; auto.
Qed.

Theorem UniqueT4 : (∀ f, Function f -> dom(f) = R -> ran(f) ⊂ R'
  -> (∀ x y, x ∈ R -> y ∈ R -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r') -> ran(f) <> [0']
  -> Function1_1 f /\ dom(f) = R /\ ran(f) = R'
    /\ (∀ x y, x ∈ R -> y ∈ R -> (x ≤ y)%r -> (f[x] ≤ f[y])%r')).
Proof.
  assert (H:True) by auto. intros.
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (QeqQ: (@Real_Axioms.Q R1) = Q) by auto.
  assert (QeqQ': (@Real_Axioms.Q R2) = Q') by auto.
  pose proof H0. apply UniqueT1 in H5 as []; auto.
  assert (∀ m, m ∈ R -> f[m] ∈ R').
  { intros. rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert (Function1_1 f) as [].
  { split; auto. split; unfold Relation; intros.
    - apply AxiomII in H8 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H8 as [_],H9 as [_].
      pose proof H8. apply Property_ran,H2 in H10.
      pose proof H8; pose proof H9.
      apply Property_dom in H11,H12. rewrite H1 in H11,H12.
      apply Property_Fun in H8,H9; auto.
      assert (f[y] + f[(-z)%r] = 0').
      { rewrite UniqueT2_Lemma3,<-H8,<-H9,Minus_P1'; auto. }
      pose proof H11. apply (H3 y (-z)%r) in H14 as [];
      auto with real. rewrite H13 in H14. apply NNPP; intro.
      assert (y - z <> 0)%r.
      { intro. assert (y - z + z = 0 + z)%r. { rewrite H17; auto. }
        rewrite <-Plus_P3,(Plus_P4 _ z),Minus_P1,(Plus_P4 0),
        Plus_P1,Plus_P1 in H18; auto with real. }
      assert (f[(y - z)%r] <> 0'); auto.
      { apply UniqueT2_Lemma4; auto with real. } }
  assert (ran(f) = R').
  { apply AxiomI; split; auto. intros.
    set (A := \{ λ u, u ∈ Q' /\ u ≤ z \}).
    pose proof H10. apply UniqueT4_Lemma1 in H11.
    set (B := \{ λ u, u ∈ Q /\ f[u] ∈ A \}). pose proof H0.
    assert (Hb : B ⊂ R).
    { unfold Included; intros.
      apply AxiomII in H13 as [_[]]; auto with real. }
    apply UniqueT3 in H12 as [_[[][H14[H15 _]]]]; auto.
    assert (Function1_1 (f|(B)) /\ dom(f|(B)) = B
      /\ ran(f|(B)) = A) as [[][]].
    { assert (Function (f|(B))). { apply MKT126a; auto. }
      assert (∀ g g1, Function g -> g1 ⊂ g -> Function g1).
      { intros. destruct H17. split; unfold Relation; intros.
        apply H18,H17 in H20; auto. apply (H19 x); auto. }
      assert (Function1_1 (f|(B))).
      { split; auto. apply (H17 (f|(Q))⁻¹); auto.
        unfold Included; intros. apply AxiomII in H18
        as [H18[x[y[]]]]. apply MKT4' in H20 as [].
        apply AxiomII; split; auto. exists x,y. split; auto.
        apply MKT4'; split; auto. apply AxiomII' in H21 as [H21[]].
        apply AxiomII'; repeat split; auto.
        apply AxiomII in H22; tauto. }
      split; auto. destruct H18. assert (dom(f|(B)) = B).
      { apply MKT30 in Hb. rewrite MKT126b,H1; auto. }
      split; auto. apply AxiomI; split; intros.
      apply Einr in H21 as [x[]]; auto. rewrite MKT126c in H22; auto.
      rewrite H20 in H21. apply AxiomII in H21 as [_[]].
      rewrite H22; auto. apply AxiomII; split; eauto. pose proof H21.
      apply AxiomII in H22 as [_[]]. rewrite <-H15 in H22.
      apply Einr in H22 as [x[]]; auto. rewrite MKT126c in H24; auto.
      exists x. assert (x ∈ dom(f|(B))).
      { rewrite H20. apply AxiomII; repeat split;
        [ |rewrite <-H14|rewrite <-H24]; eauto. }
      rewrite <-(MKT126c f B) in H24; auto. rewrite H24.
      apply Property_Value; auto. }
    assert (B <> Φ /\ ∃ c, Upper B c ) as [].
    { pose proof OrderPM_Co9'. apply (OrderPM_Co1' _ _ (-1'))
      in H20; auto with real'. rewrite Minus_P1',Plus_P4',
      Plus_P1' in H20; auto with real'.
      apply (OrderPM_Co1' _ _ z) in H20; auto with real'.
      rewrite (Plus_P4' 0'),Plus_P1' in H20; auto with real'.
      apply Arch_P9' in H20 as [q[H20[_]]]; auto with real'.
      pose proof H10. apply Arch_P10' in H22 as [n[[H22[_]]_]];
      auto. apply (Int_P1a' n 1'),Z_Subset_Q' in H22;
      auto with real'. split. assert (q ∈ A).
      { apply AxiomII; split; eauto. destruct H21; auto. }
      rewrite <-H19 in H24. rewrite reqdi in H24.
      apply Property_Value,Property_ran in H24; auto.
      rewrite <-deqri,H18 in H24. apply NEexE; eauto.
      rewrite QeqQ, QeqQ' in *.
      rewrite <-H15 in H22. apply Einr in H22 as [x[]]; auto.
      exists x. repeat split; auto. rewrite H14 in H22;
      auto with real. intros. pose proof H25. rewrite <-H18 in H26.
      apply Property_Value,Property_ran in H26; auto.
      rewrite H19 in H26. apply AxiomII in H26 as [_[]].
      rewrite MKT126c in H24,H27; auto; [ |rewrite H18; auto].
      assert (f[x0] < f[x]).
      { rewrite H14 in H22. rewrite H24 in H23.
        apply (Order_Co2' _ z); auto with real. }
      apply UniqueT4_Lemma2 in H28; auto. destruct H28; auto.
      rewrite H14 in H22. auto with real. }
    apply SupT in H21 as [y[]]; auto.
    assert (Sup1' ran(f|(B)) f[y]).
    { apply UniqueT4_Lemma3; auto. unfold Included; intros.
      apply AxiomII in H23; tauto. destruct H21 as [[_[]]]; auto. }
    apply Sup_Corollary' in H11,H23. rewrite H19 in H23.
    assert (z = f[y]).
    { apply (Min_Corollary' (\{ λ u, Upper' A u \})); auto. }
    rewrite H24. apply (@ Property_ran y),Property_Value; auto.
    rewrite H1. destruct H21 as [[_[]]]; auto. }
  split; [split|split; [ |split]]; auto. intros.
  destruct (classic (x = y)). rewrite H14. apply Leq_P1'; auto.
  apply UniqueT4_Lemma2; auto. split; auto.
Qed.

Lemma UniqueT5_Lemma1 : ∃ f, Function1_1 f /\ dom(f) = N
  /\ ran(f) = N' /\ (∀ m n, m ∈ N -> n ∈ N
    -> (m < n)%r <-> f[m] < f[n]).
Proof.
  assert (NeqN: (@Real_Axioms.N R1) = N) by auto.
 assert (NeqN': (@Real_Axioms.N R2) = N') by auto.
  set (L1 := \{\ λ u v, u ∈ N /\ v ∈ N /\ (u < v)%r \}\).
  assert (WellOrdered L1 N).
  { split; unfold Connect; intros. pose proof H.
    apply N_Subset_R in H1. apply (Order_Co1 v) in H1
    as [H1|[]]; auto with real. right; left.
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    left. apply AxiomII'; split; auto. apply MKT49a; eauto.
    apply Nat_P7 in H as [n[H[]]]; auto. exists n. split; auto.
    intros. intro. apply AxiomII' in H4 as [_[H4[H5[]]]].
    apply H2 in H3. apply H7,Leq_P2; auto with real. }
  set (L2 := \{\ λ u v, u ∈ N' /\ v ∈ N' /\ u < v \}\).
  assert (WellOrdered L2 N').
  { split; unfold Connect; intros. pose proof H0.
    apply N_Subset_R' in H2. apply (Order_Co1' v) in H2
    as [H2|[]]; auto with real'. right; left.
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    left. apply AxiomII'; split; auto. apply MKT49a; eauto.
    apply Nat_P7' in H0 as [n[H0[]]]; auto. exists n. split; auto.
    intros. intro. apply AxiomII' in H5 as [_[H5[H6[]]]].
    apply H3 in H4. apply H8,Leq_P2'; auto with real'. }
  apply (@ MKT99 L1 L2 N N') in H0 as [f[H0[[_[_[H1[]]]]]]]; auto.
  pose proof H1. apply MKT96 in H5 as [[_]].
  destruct H2 as [H2[_]], H3 as [H3[_]].
  assert (dom(f) = N /\ ran(f) = N') as [].
  { destruct H4; split; auto; apply AxiomI; split; intros; auto;
    apply NNPP; intro.
    - assert ((N' ~ ran(f)) <> Φ /\ (N' ~ ran(f)) ⊂ N') as [].
      { split. apply NEexE. exists z. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. unfold Included; intros.
        apply MKT4' in H11; tauto. }
      apply Nat_P7' in H12 as [n[H12[]]]; auto.
      assert ((∃ x, Upper' ran(f) x)).
      { exists n. repeat split; auto; intros. unfold Included;
        auto with real'. apply MKT4' in H13 as []. pose proof H13.
        apply N_Subset_R',(Order_Co1' x) in H17 as [H17|[]]; auto;
        auto with real'. destruct H17; auto. apply (H8 n) in H15;
        auto. apply AxiomII in H16 as []. elim H18; auto.
        apply AxiomII'; split; auto. apply MKT49a; eauto.
        rewrite H17. apply Leq_P1'; auto with real'. }
      apply Arch_P3a' in H15 as [m[H15[]]]; unfold Included;
      auto with real'. elim Arch_P2. rewrite NeqN, NeqN' in *. rewrite <-H4.
      exists (f⁻¹[m]). pose proof H16. rewrite reqdi in H18.
      apply Property_Value,Property_ran in H18; auto.
      rewrite <-deqri in H18. repeat split; unfold Included;
      auto with real. intros. pose proof H19.
      apply Property_Value,Property_ran in H20; auto.
      pose proof H20. apply H17 in H20.
      destruct (classic (f[x] = m)). rewrite <-H22,f11iv; auto.
      assert (Rrelation f[x] L2 m).
      { apply AxiomII'; repeat split; auto. apply MKT49a; eauto. }
      destruct H6 as [_[_[_]]]. apply H6 in H23; try rewrite
      <-reqdi; auto. apply AxiomII' in H23 as [_[H23[]]].
      rewrite f11iv in H25; auto. destruct H25; auto. apply NEexE.
      exists f[1]. apply (@ Property_ran 1),Property_Value; auto.
      rewrite H4; auto with real.
    - assert ((N ~ dom(f)) <> Φ /\ (N ~ dom(f)) ⊂ N) as [].
      { split. apply NEexE. exists z. apply MKT4'; split; auto.
        apply AxiomII; split; eauto. unfold Included; intros.
        apply MKT4' in H11; tauto. }
      apply Nat_P7 in H12 as [n[H12[]]]; auto.
      assert ((∃ x, Upper dom(f) x)).
      { exists n. repeat split; auto; intros. unfold Included;
        auto with real. apply MKT4' in H13 as []. pose proof H13.
        apply N_Subset_R,(Order_Co1 x) in H17 as [H17|[]]; auto;
        auto with real. destruct H17; auto. apply (H7 n) in H15;
        auto. apply AxiomII in H16 as []. elim H18; auto.
        apply AxiomII'; split; auto. apply MKT49a; eauto.
        rewrite H17. apply Leq_P1; auto with real. }
      apply Arch_P3a in H15 as [m[H15[]]]; unfold Included;
      auto with real. elim Arch_P2'. rewrite NeqN' in *. rewrite <-H4.
      exists (f[m]). pose proof H16.
      apply Property_Value,Property_ran in H18; auto.
      repeat split; unfold Included; auto with real'. intros.
      pose proof H19. rewrite reqdi in H20.
      apply Property_Value,Property_ran in H20; auto.
      pose proof H20. rewrite <-deqri in H21. apply H17 in H21.
      destruct (classic (f⁻¹[x] = m)). rewrite <-H22,f11vi; auto.
      assert (Rrelation f⁻¹[x] L1 m).
      { apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
        rewrite <-deqri in H20; auto. }
      destruct H1 as [_[_[_]]]. apply H1 in H23; auto;
      try rewrite deqri; auto. apply AxiomII' in H23 as [_[H23[]]].
      rewrite f11vi in H25; auto. destruct H25; auto. apply NEexE.
      exists f⁻¹[1']. rewrite deqri.
      apply (@ Property_ran 1'),Property_Value; auto.
      rewrite <-reqdi,H4; auto with real'. }
  exists f. split; [split|split; [ |split]]; auto.
  assert (∀ m n, m ∈ N -> n ∈ N -> (m < n)%r -> f[m] < f[n]).
  { intros. destruct H1 as [_[_[_]]]. rewrite H9 in H1.
    assert (Rrelation m L1 n).
    { apply AxiomII'; split; try apply MKT49a; eauto. }
    apply H1 in H14; auto. apply AxiomII' in H14; tauto. }
  split; auto; intros. pose proof H12. apply N_Subset_R in H15.
  apply (Order_Co1 n) in H15 as [H15|[]]; auto with real.
  apply H11 in H15; auto. destruct H14,H15. elim H17.
  apply Leq_P2'; auto; apply N_Subset_R'; rewrite NeqN,NeqN' in *;
  rewrite <-H10; [apply (@ Property_ran n)|apply (@ Property_ran m)];
  apply Property_Value; auto; rewrite H9; auto.
  rewrite H15 in H14. destruct H14; contradiction.
Qed.

Lemma UniqueT5_Lemma2 : ∀ f,
  Function1_1 f -> dom(f) = N -> ran(f) = N'
  -> (∀ m n, m ∈ N -> n ∈ N -> (m < n)%r <-> f[m] < f[n])
  -> (∀ m n, m ∈ N -> n ∈ N -> f[(m + n)%r] = f[m] + f[n]
    /\ f[(m · n)%r] = f[m] · f[n] /\ ((m < n)%r
      -> f[(n - m)%r] = f[n] - f[m])) /\ f[1] = 1'.
Proof.
  intros f [] H1 H2 H3.
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (NeqN: (@Real_Axioms.N R1) = N) by auto.
  assert (NeqN': (@Real_Axioms.N R2) = N') by auto.
  assert ((∀ m, m ∈ N -> f[m] ∈ N')
    /\ (∀ m, m ∈ N -> f[m] ∈ R')) as [].
  { split; intros; rewrite <-H1 in H4;
    apply Property_Value,Property_ran in H4; auto.
    rewrite <-H2; auto. rewrite H2 in H4; auto with real'. }
  assert (f[1] = 1').
  { pose proof one_in_R_Co'. rewrite ReqR' in *;
    apply (Order_Co1' f[1]) in H6
    as [H6|[]]; auto.
    destruct one_is_min_in_N' as [_[]]. pose proof one_in_N.
    apply H4,H8 in H9. destruct H6. apply Leq_P2';
    auto with real real'. pose proof one_in_N'. rewrite NeqN' in *;
    rewrite <-H2 in H7. apply Einr in H7 as [x[]]; auto.
    rewrite H1 in H7. rewrite H8 in H6. apply H3 in H6;
    auto with real. destruct one_is_min_in_N as [_[]].
    pose proof H7. apply H10 in H7. destruct H6. elim H12.
    apply Leq_P2; auto with real. }
  assert (∀ m, m ∈ N -> f[(m + 1)%r] = f[m] + f[1]).
  { intros. assert (f[m] < f[(m + 1)%r]).
    { apply H3; auto with real. pose proof OrderPM_Co9.
      apply (OrderPM_Co1 _ _ m) in H8; auto with real.
      rewrite Plus_P4,Plus_P1,Plus_P4 in H8; auto with real. }
    assert (f[(m + 1)%r] ∈ R'). auto with real.
    apply (Order_Co1' (f[m] + f[1])) in H9 as [H9|[]];
    auto with real real'. rewrite H6 in H9.
    assert ((f[m] + 1') ∈ N'). auto with real'.
    rewrite <-H2 in H10. apply Einr in H10 as [x[]]; auto.
    pose proof OrderPM_Co9'. apply (OrderPM_Co1' _ _ (f[m]))
    in H12; auto with real'. rewrite Plus_P4',Plus_P1',Plus_P4'
    in H12; auto with real'. rewrite H11 in H12. rewrite H1 in H10.
    apply H3 in H12; auto. apply Nat_P4 in H12; auto.
    destruct (classic ((m + 1)%r = x)). rewrite H13,H6; auto.
    assert (m + 1 < x)%r. split; auto. apply H3 in H14;
    auto with real. rewrite H11 in H9.
    assert (f[x] < f[x]) as []; try contradiction.
    { destruct H14. apply (Order_Co2' _ (f[(m + 1)%r]));
      auto with real. }
    apply Nat_P4' in H9; auto with real real'. rewrite H6 in H9.
    apply (OrderPM_Co1' _ _ 1') in H8 as []; auto with real real'.
    elim H10. apply Leq_P2'; auto with real real'. }
  assert (∀ m, m ∈ N -> (1 < m)%r -> f[(m - 1)%r] = f[m] - f[1]).
  { intros. assert (f[(m - 1)%r] < f[m]).
    { apply H3; auto. apply Nat_P2; destruct H9; auto.
      pose proof OrderPM_Co9. apply (OrderPM_Co1 _ _ (-(1))%r)
      in H10; auto with real. rewrite Minus_P1,Plus_P4,Plus_P1
      in H10; auto with real. apply (OrderPM_Co1 _ _ m) in H10;
      auto with real. rewrite (Plus_P4 0),Plus_P1,Plus_P4 in H10;
      auto with real. }
    assert (f[(m - 1)%r] ∈ N').
    { apply H4,Nat_P2; destruct H9; auto. }
    assert ((f[m] - 1') ∈ N').
    { apply Nat_P2'; auto. apply H3 in H9 as []; auto with real.
      rewrite H6 in H12; auto. }
    pose proof H11. apply N_Subset_R',(Order_Co1' (f[m] - f[1]))
    in H13 as [H13|[]]; auto with real real'. rewrite H6 in H13.
    apply Nat_P4' in H13; auto. rewrite <-Plus_P3',(Plus_P4' (-1')),
    Minus_P1',Plus_P1' in H13; auto with real'. destruct H10.
    elim H14. apply Leq_P2'; auto with real'. rewrite H6 in H13.
    rewrite <-H2 in H12. apply Einr in H12 as [x[]]; auto.
    rewrite H14 in H13. assert ((m - 1)%r ∈ N).
    { apply Nat_P2; destruct H9; auto. }
    rewrite H1 in H12. apply H3 in H13; auto.
    assert (x < m)%r.
    { apply H3; auto. replace f[m] with (0' + f[m]).
      rewrite <-H14,Plus_P4'; auto with real'.
      rewrite Plus_P4',Plus_P1'; auto with real'. }
    destruct H9. apply Nat_P6 in H8; auto. elim H8; eauto. }
  set (E := \{ λ u, u ∈ N /\ (∀ m, m ∈ N -> f[(m + u)%r]
    = f[m] + f[u] /\ ((u < m)%r -> f[(m - u)%r] = f[m] - f[u])) \}).
  assert (E ⊂ N /\ 1 ∈ E) as [].
  { split. unfold Included; intros. apply AxiomII in H9; tauto.
    apply AxiomII; repeat split; eauto with real. }
  assert (E = N).
  { apply MathInd; auto. intros. apply AxiomII in H11 as [_[]].
    apply AxiomII; repeat split; eauto with real.
    - assert (m + 1 ∈ N)%r. auto with real. apply H12 in H14
      as [H14 _]. rewrite H7,(Plus_P4 x),Plus_P3,H14,H7,
      (Plus_P4' f[x]),Plus_P3'; auto with real.
    - intros. rewrite PlusMult_Co3,Mult_P4,Mult_P5,Mult_P4,
      <-PlusMult_Co3,Mult_P4,Mult_P1,(Plus_P4 (-x)%r),Plus_P3;
      auto with real. assert (1 < m)%r.
      { apply (Order_Co2 _ (x + 1)%r); auto with real. left.
        split; [ |destruct H14; auto]. assert (0 < x)%r.
        { apply (Order_Co2 _ 1); auto with real. left.
          split; auto with real. destruct one_is_min_in_N
          as [_[]]; auto. }
        apply (OrderPM_Co1 _ _ 1) in H15; auto with real.
        rewrite Plus_P4,Plus_P1 in H15; auto with real. }
      apply (OrderPM_Co1 _ _ (-(1))%r) in H14; auto with real.
      rewrite <-Plus_P3,Minus_P1,Plus_P1 in H14; auto with real.
      apply H12 in H14; [ |apply Nat_P2; destruct H15]; auto.
      rewrite ReqR, ReqR' in *;
      rewrite H14,H8,H7,(PlusMult_Co3' (f[x] + f[1])),Mult_P4',
      Mult_P5',Mult_P4',<-PlusMult_Co3',Mult_P4',H6,Mult_P1',
      (Plus_P4' (-f[x])),Plus_P3'; auto with real'. }
  assert (∀ m n, m ∈ N -> n ∈ N -> f [(m + n)%r] = f [m] + f [n]
    /\ ((m < n)%r -> f [(n - m)%r] = f [n] - f [m])).
  { intros. pose proof H12; pose proof H13.
    rewrite <-H11 in H12. apply AxiomII in H12 as [_[]].
    apply H16 in H13 as []. split; auto.
    rewrite Plus_P4,Plus_P4'; auto with real. }
  set (F := \{ λ u, u ∈ N /\ (∀ m, m ∈ N -> f[(m · u)%r]
    = f[m] · f[u]) \}).
  assert (F ⊂ N /\ 1 ∈ F) as [].
  { split. unfold Included; intros. apply AxiomII in H13; tauto.
    apply AxiomII; repeat split; eauto with real. intros.
    rewrite Mult_P1,H6,Mult_P1'; auto with real. }
  assert (F = N).
  { apply MathInd; auto. intros. apply AxiomII in H15 as [_[]].
    apply AxiomII; repeat split; eauto with real. intros.
    rewrite Mult_P4,Mult_P5,(Mult_P4 1),Mult_P1,H7,Mult_P4',
    Mult_P5',Mult_P4',<-H16,H6,Mult_P4',Mult_P1',Mult_P4;
    auto with real real'. apply H12; auto with real. }
  split; auto. intros; repeat split; try apply H12; auto.
  rewrite <-H15 in H17. apply AxiomII in H17 as [_[]]; auto.
Qed.

Lemma UniqueT5_Lemma3 : ∃ f, Function f /\ dom(f) = Z
  /\ ran(f) ⊂ Z' /\ f[0] = 0' /\ f[1] = 1'
  /\ (∀ m n, m ∈ Z -> n ∈ Z -> f[(m + n)%r] = f[m] + f[n]
    /\ f[(m · n)%r] = f[m] · f[n])
  /\ (∀ m, m ∈ Z -> m <> 0 -> f[m] <> 0')
  /\ (∀ m, m ∈ Z -> (0 < m)%r -> 0' < f[m]).
Proof.
  assert (NeqN: (@Real_Axioms.N R1) = N) by auto.
  assert (NeqN': (@Real_Axioms.N R2) = N') by auto.
  assert (ZeqZ: (@Real_Axioms.Z R1) = Z) by auto.
  assert (ZeqZ': (@Real_Axioms.Z R2) = Z') by auto.
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  destruct UniqueT5_Lemma1 as [f[[][H1[]]]]. pose proof H3 as H3a.
  apply UniqueT5_Lemma2 in H3 as []; try split; auto.
  set (g := \{\ λ u v, (u ∈ N /\ v = f[u])
    \/ (u ∈ \{ λ a, (-a)%r ∈ N \} /\ v = -f[(-u)%r])
    \/ (u = 0 /\ v = 0') \}\).
  assert (∀ m, ~ (m ∈ N /\ ((-m)%r) ∈ N)).
  { intros; intro. destruct H5.
    assert (0 < m /\ 0 < -m)%r as [].
    { destruct one_is_min_in_N as [_[]].
      split; apply (Order_Co2 _ 1); auto with real. }
    apply OrderPM_Co2a in H7; auto with real.
    destruct H7,H8. apply H10,Leq_P2; auto with real. }
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H6 as [_[[]|[[]|[]]]],
    H7 as [_[[]|[[]|[]]]]; try rewrite H8,H9; auto.
    apply AxiomII in H7 as []. elim (H5 x); auto.
    elim zero_not_in_N. rewrite <-H7; auto.
    apply AxiomII in H6 as []. elim (H5 x); auto.
    apply AxiomII in H6 as []. rewrite H7,PlusMult_Co3,
    PlusMult_Co1 in H10; auto with real.
    elim zero_not_in_N; auto. rewrite H6 in H7.
    elim zero_not_in_N; auto. apply AxiomII in H7 as [].
    rewrite H6,PlusMult_Co3,PlusMult_Co1 in H10; auto with real.
    elim zero_not_in_N; auto. }
  assert (dom(g) = Z).
  { apply AxiomI; split; intros.
    apply Property_Value,AxiomII' in H7 as [_[[]|[[]|[]]]];
    auto with real. apply MKT4; right. apply MKT4; auto.
    rewrite H7. repeat (apply MKT4; right).
    apply MKT41; eauto with real. apply AxiomII; split; eauto.
    apply MKT4 in H7 as []. exists f[z].
    apply AxiomII'; split; auto. apply MKT49a; eauto.
    rewrite NeqN in *; rewrite <-H1 in H7.
    apply Property_Value,Property_ran in H7; eauto.
    apply MKT4 in H7 as []. pose proof H7.
    apply AxiomII in H7 as []. exists (-f[(-z)%r]).
    apply AxiomII'; split; auto. apply MKT49a; auto. rewrite NeqN in *; 
    rewrite <-H1 in H9. apply Property_Value,Property_ran in H9;
    auto. rewrite H2 in H9. eauto with real'. exists 0'.
    apply MKT41 in H7; eauto with real. rewrite H7.
    apply AxiomII'; split; auto.
    apply MKT49a; eauto with real real'. }
  assert (ran(g) ⊂ Z').
  { unfold Included; intros. apply AxiomII in H8 as [_[]].
    apply AxiomII' in H8 as [_[[]|[[]|[]]]]. rewrite H9.
    apply N_Subset_Z'. rewrite NeqN' in *; rewrite <-H2. rewrite <-H1 in H8.
    apply Property_Value,Property_ran in H8; auto.
    apply MKT4; right. apply MKT4; left. apply AxiomII.
    apply AxiomII in H8 as []. rewrite <-H1 in H10.
    apply Property_Value,Property_ran in H10; auto.
    rewrite H2 in H10. rewrite PlusMult_Co3',H9,PlusMult_Co4';
    try rewrite H9; auto with real'. split; eauto with real'.
    rewrite H9. repeat (apply MKT4; right).
    apply MKT41; eauto with real'. }
  assert (g[0] = 0').
  { assert (0 ∈ Z).
    { repeat (apply MKT4; right). apply MKT41; eauto with real. }
    rewrite <-H7 in H9. apply Property_Value,AxiomII' in H9
    as [_[[]|[[]|[]]]]; auto. elim zero_not_in_N; auto.
    apply AxiomII in H9 as []. rewrite PlusMult_Co3,PlusMult_Co1
    in H11; auto with real. elim zero_not_in_N; auto. }
  assert (g[1] = 1').
  { pose proof one_in_N. apply N_Subset_Z in H10. rewrite ZeqZ in *;
    rewrite <-H7 in H10. apply Property_Value,AxiomII' in H10
    as [_[[]|[[]|[]]]]; auto. rewrite <-H4; auto.
    apply AxiomII in H10 as []. elim (H5 1); auto with real.
    destruct OrderPM_Co9. elim H13; auto. }
  exists g. split; [ |split; [ |split; [ |split; [ |split]]]]; auto.
  assert (∀ m, m ∈ N -> g[m] = f[m]).
  { intros. pose proof H11. apply N_Subset_Z in H11. rewrite ZeqZ in *;
    rewrite <-H7 in H11. apply Property_Value,AxiomII' in H11
    as [_[[]|[[]|[]]]]; auto. apply AxiomII in H11 as [].
    elim (H5 m); auto. rewrite H11 in H12.
    elim zero_not_in_N; auto. }
  assert (∀ m, m ∈ \{ λ a, (-a)%r ∈ N \} -> g[m] = -f[(-m)%r]).
  { intros. assert (m ∈ Z).
    { apply MKT4; right; apply MKT4; auto. }
    rewrite <-H7 in H13. apply Property_Value,AxiomII' in H13
    as [_[[]|[[]|[]]]]; auto. apply AxiomII in H12 as [].
    elim (H5 m); auto. apply AxiomII in H12 as [].
    rewrite H13,PlusMult_Co3,PlusMult_Co1 in H15; auto with real.
    elim zero_not_in_N; auto. }
  assert (∀ m, m ∈ N -> f[m] ∈ N').
  { intros. rewrite <-H1 in H13. rewrite <-H2.
    apply Property_Value,Property_ran in H13; auto. }
  assert (∀ m n, m ∈ N -> n ∈ \{ λ a, (-a)%r ∈ N \}
    -> g[(m + n)%r] = g[m] + g[n] /\ g[(m · n)%r] = g[m] · g[n]).
  { intros. assert (n ∈ Z).
    { apply MKT4; right; apply MKT4; auto. }
    assert ((m · n)%r ∈ \{ λ a, (-a)%r ∈ N \}) as Ha.
    { apply AxiomII; split; eauto with real.
      apply AxiomII in H15 as [].
      rewrite PlusMult_Co3,Mult_P3,(Mult_P4 _ m),<-Mult_P3,
      <-PlusMult_Co3; auto with real. }
    assert ((m + n)%r ∈ Z). auto with real.
    apply MKT4 in H17 as []. assert (0 < (m + n))%r.
    { apply (Order_Co2 _ 1); auto with real. left.
      destruct one_is_min_in_N as [_[_]]; auto with real. }
    apply (OrderPM_Co1 _ _ (-n)%r) in H18; auto with real.
    rewrite Plus_P4,Plus_P1,<-Plus_P3,Minus_P1,Plus_P1 in H18;
    auto with real. pose proof H15. apply AxiomII in H19 as [_].
    apply H3 in H18; auto. rewrite PlusMult_Co3,PlusMult_Co4 in H18;
    auto with real. rewrite H11,H11,H12,H18; auto. split; auto.
    rewrite PlusMult_Co3',Mult_P3',(Mult_P4' f[m]),<-Mult_P3',
    <-PlusMult_Co3'; auto with real'.
    pose proof H19. apply (H3 m) in H20 as [_[H20 _]]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite <-H20,PlusMult_Co3,Mult_P3,(Mult_P4 m (-(1))%r),
    <-Mult_P3,<-PlusMult_Co3,H12; auto with real.
    apply MKT4 in H17 as []. pose proof H17.
    apply AxiomII in H18 as [_]. assert (0 < (-(m + n)))%r.
    { destruct one_is_min_in_N as [_[_]].
      apply (Order_Co2 _ 1); auto with real. }
    rewrite PlusMult_Co3,Plus_P4,Mult_P4,Mult_P5,Mult_P4,
    <-PlusMult_Co3,Mult_P4,<-PlusMult_Co3 in H19; auto with real.
    apply (OrderPM_Co1 _ _ m) in H19; auto with real.
    rewrite Plus_P4,Plus_P1,<-Plus_P3,(Plus_P4 _ m),Minus_P1,
    Plus_P1 in H19; auto with real. pose proof H15.
    apply AxiomII in H20 as [_]. apply H3 in H19; auto.
    rewrite H12,H11,H12; auto. split. rewrite ReqR, ReqR' in *.
    rewrite PlusMult_Co3,Mult_P4,Mult_P5,Mult_P4,<-PlusMult_Co3,
    Mult_P4,<-PlusMult_Co3,Plus_P4,H19,PlusMult_Co3',Mult_P4',
    Mult_P5',Mult_P4',<-PlusMult_Co3',Mult_P4',PlusMult_Co4',
    Plus_P4'; auto with real real'.
    rewrite PlusMult_Co3',Mult_P3',(Mult_P4' f[m]),<-Mult_P3',
    <-PlusMult_Co3',H12; auto with real'.
    pose proof H20. apply (H3 m) in H21 as [_[]]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite PlusMult_Co3,Mult_P3,(Mult_P4 _ m),<-Mult_P3,
    <-PlusMult_Co3,H21; auto with real.
    apply MKT41 in H17; eauto with real. pose proof H17.
    rewrite Plus_P4 in H17; auto with real.
    apply Plus_Co3 in H17; auto with real.
    rewrite Plus_P4,Plus_P1 in H17; auto with real.
    rewrite ReqR, ReqR' in *.
    rewrite H18,H9,H11,H12,<-H17,Minus_P1'; auto with real'.
    rewrite H12,PlusMult_Co3,Mult_P4,<-Mult_P3,(Mult_P4 n),
    <-PlusMult_Co3,<-H17; auto with real.
    pose proof H14. apply (H3 m m) in H19 as [_[]]; auto.
    rewrite H19,PlusMult_Co3',Mult_P3',<-PlusMult_Co3',
    Mult_P4'; auto with real'. }
  assert (∀ m n, m ∈ \{ λ a, (-a)%r ∈ N \}
    -> n ∈ \{ λ a, (-a)%r ∈ N \} -> g[(m + n)%r] = g[m] + g[n]
    /\ g[(m · n)%r] = g[m] · g[n]).
  { intros. assert (m ∈ Z /\ n ∈ Z) as [].
    { split; apply MKT4; right; apply MKT4; auto. }
    assert ((m + n)%r ∈ \{ λ a, (-a)%r ∈ N \}).
    { apply AxiomII in H15 as [_],H16 as [_].
      apply AxiomII; split; eauto with real.
      rewrite PlusMult_Co3,Mult_P4,Mult_P5,Mult_P4,
      <-PlusMult_Co3,Mult_P4,<-PlusMult_Co3; auto with real. }
    assert (m · n = -m · -n)%r.
    { rewrite ReqR, ReqR' in *.
      rewrite PlusMult_Co3,(PlusMult_Co3 n),Mult_P3,
      (Mult_P4 _ m),<-(Mult_P3 m),PlusMult_Co5,Mult_P1,
      Mult_P1; auto with real. }
    assert ((m · n)%r ∈ N).
    { apply AxiomII in H15 as [_],H16 as [_].
      rewrite H20; auto with real. }
    rewrite H12,H12,H12,H11; auto. split.
    rewrite PlusMult_Co3,Mult_P4,Mult_P5,Mult_P4,<-PlusMult_Co3,
    Mult_P4,<-PlusMult_Co3; auto with real.
    apply AxiomII in H15 as [_],H16 as [_].
    pose proof H16. apply (H3 (-m)%r) in H22 as [H22 _]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite H22,PlusMult_Co3',Mult_P4',Mult_P5',Mult_P4',
    <-PlusMult_Co3',Mult_P4',<-PlusMult_Co3'; auto with real'.
    apply AxiomII in H15 as [_],H16 as [_].
    pose proof H16. apply (H3 (-m)%r) in H22 as [_[H22 _]]; auto.
    rewrite ReqR, ReqR' in *.
    rewrite H20,H22,PlusMult_Co3',(PlusMult_Co3' f[(-n)%r]),
    Mult_P3',(Mult_P4' (-1')),<-(Mult_P3' _ (-1') (-1')),
    PlusMult_Co4',Mult_P1'; auto with real'. }
  assert (∀ m, m ∈ Z -> g[m] ∈ Z').
  { intros. rewrite <-H7 in H16.
    apply Property_Value,Property_ran in H16; auto. }
  split; intros. pose proof H17; pose proof H18.
  apply MKT4 in H19 as []. apply MKT4 in H20 as [].
  rewrite H11,H11,H11,H11; auto with real.
  apply (H3 m n) in H19; tauto. apply MKT4 in H20 as [].
  apply (H14 m n) in H19; auto. apply MKT41 in H20; eauto with real.
  rewrite H20,Plus_P1,PlusMult_Co1,H9,Plus_P1',PlusMult_Co1';
  auto with real real'. apply MKT4 in H19 as [].
  apply MKT4 in H20 as []. rewrite Plus_P4,Plus_P4',
  Mult_P4,Mult_P4'; auto with real real'.
  apply MKT4 in H20 as []; auto.
  apply MKT41 in H20; eauto with real.
  rewrite H20,Plus_P1,PlusMult_Co1,H9,Plus_P1',PlusMult_Co1';
  auto with real real'. apply MKT41 in H19; eauto with real.
  rewrite H19,H9,Plus_P4,Plus_P1,Plus_P4',Plus_P1',Mult_P4,
  PlusMult_Co1,Mult_P4',PlusMult_Co1'; auto with real real'.
  split; intros. apply MKT4 in H17 as []. rewrite H11; auto.
  rewrite NeqN, NeqN' in *.
  rewrite <-H1 in H17. apply Property_Value,Property_ran
  in H17; auto. rewrite H2 in H17.
  assert (0' < f[m]) as []; auto.
  { destruct one_is_min_in_N' as [_[]].
    apply (Order_Co2' _ 1'); auto with real'. }
  apply MKT4 in H17 as []. rewrite H12; auto.
  apply AxiomII in H17 as []. rewrite NeqN, NeqN' in *. rewrite <-H1 in H19.
  apply Property_Value,Property_ran in H19; auto.
  rewrite H2 in H19. assert (0' < f[(-m)%r]).
  { destruct one_is_min_in_N' as [_[]].
    apply (Order_Co2' _ 1'); auto with real'. }
  apply (OrderPM_Co1' _ _ (-f[(-m)%r])) in H20; auto with real'.
  rewrite Plus_P4',Plus_P1',Minus_P1' in H20; auto with real'.
  destruct H20; auto. apply MKT41 in H17; eauto with real.
  assert (m ∈ N).
  { pose proof H17. apply MKT4 in H17 as []; auto.
    apply MKT4 in H17 as []. apply AxiomII in H17 as [].
    apply OrderPM_Co2a in H18; auto with real.
    assert (0 < (-m))%r.
    { destruct one_is_min_in_N as [_[_]].
      apply (Order_Co2 _ 1); auto with real. }
    assert (0 < 0)%r as []; try contradiction.
    { apply (Order_Co2 _ (-m)%r); destruct H21; auto with real. }
    apply MKT41 in H17; eauto with real. rewrite H17 in H18.
    destruct H18; contradiction. }
  destruct (classic (m = 1)). rewrite H20,H10; auto with real'.
  assert (1 < m)%r.
  { split; auto. destruct one_is_min_in_N as [_[]]; auto. }
  apply H3a in H21; auto with real. rewrite <-H11 in H21; auto with real.
  rewrite H10 in H21. rewrite H11; auto. destruct H21.
  apply (Order_Co2' _ 1'); auto with real'.
Qed.

Lemma UniqueT5_Lemma4 : ∃ f, Function f /\ dom(f) = Q
  /\ ran(f) ⊂ Q' /\ f[0] = 0' /\ f[1] = 1'
  /\ (∀ a b, a ∈ Q -> b ∈ Q -> f[(a + b)%r] = f[a] + f[b]
    /\ f[(a · b)%r] = f[a] · f[b])
  /\ (∀ a b, a ∈ Q -> b ∈ Q -> (a < b)%r -> f[a] < f[b]).
Proof.
  destruct UniqueT5_Lemma3 as [f[H[H0[H1[H2[H3[H4[H5 H5a]]]]]]]].
  assert (∀ m, m ∈ (Z ~ [0]) -> f[m] ∈ (Z' ~ [0'])).
  { intros. apply MKT4' in H6 as []. apply AxiomII in H7 as [].
    pose proof H6. rewrite <-H0 in H6.
    apply Property_Value,Property_ran in H6; auto.
    apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H10; eauto with real'. apply NNPP in H10.
    apply H10,H5; auto. intro. elim H8. apply MKT41; eauto with real. }
  assert (∀ m, m ∈ Z -> f[m] ∈ Z') as H6a.
  { intros. rewrite <-H0 in H7.
    apply Property_Value,Property_ran in H7; auto. }
  assert ((Z ~ [0]) ⊂ (R ~ [0]) /\ (Z' ~ [0']) ⊂ (R' ~ [0'])) as [].
  { split; unfold Included; intros; apply MKT4' in H7 as [];
    apply MKT4'; auto with real real'. }
  assert ((Z ~ [0]) ⊂ R /\ (Z' ~ [0']) ⊂ R') as [].
  { split; unfold Included; intros; apply MKT4' in H9 as [];
    auto with real real'. }
  assert ((R ~ [0]) ⊂ R /\ (R' ~ [0']) ⊂ R') as [].
  { split; unfold Included; intros; apply MKT4' in H11; tauto. }
  assert ((Z ~ [0]) ⊂ Z /\ (Z' ~ [0']) ⊂ Z') as [].
  { split; unfold Included; intros; apply MKT4' in H13; tauto. }
  pose proof Mult_inv1; pose proof Mult_inv1'.
  assert (∀ a b c d, a ∈ Z -> b ∈ (Z ~ [0])
    -> c ∈ Z -> d ∈ (Z ~ [0]) -> (a / b = c / d)%r
    -> f[a] / f[b] = f[c] / f[d]).
  { intros. assert ((b · d) · (a / (1 ·b)) = (b · d) · (c / (1 · d)))%r.
    { rewrite (Mult_P4 1),(Mult_P4 1),Mult_P1,Mult_P1,H21;
      auto with real. }
    rewrite Mult_P3,<-(Mult_P3 b d a),(Mult_P4 b),<-Frac_P2,Divide_P2,
    Divide_P1,Mult_P1,Mult_P3,(Mult_P4 _ c),Mult_P3,<-Frac_P2,
    Divide_P2,Divide_P1,Mult_P1 in H22; auto with real;
    try (rewrite Mult_P4,Mult_P1); auto with real.
    assert (f[d · a] = f[c · b])%r. { rewrite H22; auto. }
    assert (f[(d · a)%r] = f[d] · f[a] /\ f[(c · b)%r] = f[c] · f[b])
    as []. { split; apply H4; auto. } rewrite H24,H25 in H23.
    assert ((f[d] · f[a]) / (f[d] · f[b])
      = (f[c] · f[b]) / (f[d] · f[b])). { rewrite H23; auto. }
    rewrite <-Frac_P1',(Mult_P4' f[d]),(Mult_P4' f[d]),<-Frac_P1'
    in H26; auto with real'. }
  set (g := \{\ λ u v, (∃ m n, m ∈ Z /\ n ∈ (Z ~ [0])
    /\ u = (m / n)%r /\ v = f[m] / f[n]) \}\).
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H18 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H18 as [_[m[n[H18[H20[]]]]]].
    apply AxiomII' in H19 as [_[a[b[H19[H23[]]]]]].
    rewrite H21 in H24. rewrite H22,H25; auto. }
  assert (dom(g) = Q).
  { apply AxiomI; split; intros. apply AxiomII in H19 as [H19[]].
    apply AxiomII' in H20 as [_[a[b[H20[H21[]]]]]].
    apply AxiomII; split; eauto.
    apply AxiomII in H19 as [H19[a[b[H20[]]]]].
    apply AxiomII; split; auto. exists (f[a] / f[b]).
    apply AxiomII'; split. apply MKT49a; auto. exists R'.
    apply Mult_close'; auto with real'. exists a,b; auto. }
  assert (ran(g) ⊂ Q').
  { unfold Included; intros. apply Einr in H20 as [x[]]; auto.
    apply Property_Value,AxiomII' in H20 as [_[a[b[H20[H22[]]]]]]; auto.
    rewrite H21,H24. apply AxiomII; split. exists R'.
    apply Mult_close'; auto with real'. exists f[a],f[b]. auto. }
  assert (∀ a b, a ∈ Z -> b ∈ (Z ~ [0]) -> g[(a / b)%r]
    = f[a] / f[b]).
  { intros. assert ((a / b)%r ∈ Q).
    { apply AxiomII; split; eauto. exists R. auto with real. }
    rewrite <-H19 in H23. apply Property_Value,AxiomII' in H23
    as [_[x[y[H23[H24[]]]]]]; auto. rewrite H26; auto. }
  assert (0 ∈ Z /\ 1 ∈ (Z ~ [0])) as [].
  { split. repeat (apply MKT4; right). apply MKT41; eauto with real.
    apply MKT4'; split; auto with real. apply AxiomII; split;
    eauto with real. intro. apply MKT41 in H22; eauto with real.
    destruct OrderPM_Co9; auto. }
  assert (g[0] = 0' /\ g[1] = 1') as [].
  { assert (0 = 0 / 1 /\ 1 = 1 / 1)%r as [].
    { split; rewrite Divide_P2; auto with real. }
    split; [rewrite H24|rewrite H25]; rewrite H21; auto with real;
    try rewrite H2; rewrite H3,Divide_P2'; auto with real'. }
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (∀ a b, a ∈ Q -> b ∈ Q -> g[(a + b)%r] = g[a] + g[b]
    /\ g[(a · b)%r] = g[a] · g[b]).
  { intros. apply AxiomII in H26 as [_[a1[a2[H26[]]]]].
    apply AxiomII in H27 as [_[b1[b2[H27[]]]]].
    rewrite H29,H31,H21,H21,Frac_P2; auto with real.
    assert ((a2 · b2)%r ∈ (Z ~ [0])).
    { apply MKT4' in H28 as [],H30 as [].
      apply MKT4'; split; auto with real.
      apply AxiomII; split; eauto with real. intro. apply MKT41 in H34;
      eauto with real. apply AxiomII in H32 as [_],H33 as [_].
      apply PlusMult_Co2 in H34 as []; auto; [elim H32|elim H33];
      apply MKT41; eauto with real. }
    assert (a1 / a2 + b1 / b2 = (a1 · b2 + a2 · b1) / (a2 · b2))%r.
    { rewrite Mult_P5,<-Frac_P1,(Mult_P4 a2),(Mult_P4 a2),<-Frac_P1;
      auto with real. }
    rewrite ReqR, ReqR' in *.
    rewrite H33,H21; auto with real.
    assert ((a1 · b2) ∈ Z /\ (a2 · b1) ∈ Z)%r as [].
    { split; apply Int_P1b; auto with real. }
    apply (H4 (a1 · b2)%r) in H35 as [H35 _]; auto.
    pose proof H26; pose proof H27. apply (H4 _ b2) in H36 as [_]; auto.
    apply (H4 a2) in H37 as [_]; auto. rewrite H35,H36,H37.
    pose proof H28. apply MKT4' in H38 as []. apply (H4 _ b2) in H38
    as []; auto. split. rewrite H40,Mult_P5',<-Frac_P1',
    (Mult_P4' f[a2]),(Mult_P4' f[a2]),<-Frac_P1'; auto with real'.
    apply H6,H8,Mult_inv1',MKT4' in H32 as []. apply MKT4' in H28 as [].
    apply (H4 _ b2) in H28 as []; auto. rewrite <-H43; auto.
    rewrite H21; auto with real. pose proof H26.
    apply (H4 a1 b1) in H41 as []; auto.
    rewrite H42,H40,Frac_P2'; auto with real'. }
  assert (NeqN: (@Real_Axioms.N R1) = N) by auto.
  assert (NeqN': (@Real_Axioms.N R2) = N') by auto.
  assert (∀ a, a ∈ Q -> (0 < a)%r -> 0' < g[a]).
  { intros. apply Existence_of_irRational_Number_Lemma6 in H27
    as [x[y[H27[]]]]; auto. assert (0 < x /\ 0 < y)%r as [].
    { destruct one_is_min_in_N as [_[]].
      split; apply (Order_Co2 _ 1); auto with real. }
    assert (y ∈ (Z ~ [0])).
    { apply MKT4'; split; auto with real. apply AxiomII; split;
      eauto. intro. apply MKT41 in H33; eauto with real.
      rewrite H33 in H32. destruct H32; auto. }
    rewrite H30,H21; auto with real. pose proof H31; pose proof H32.
    apply H5a in H34,H35; auto with real.
    apply OrderPM_Co5'; auto.
    rewrite ReqR, ReqR' in *.
    rewrite NeqN, NeqN' in *.
    left. split; auto. }
  assert (∀ a b, a ∈ Q -> b ∈ Q -> (a < b)%r -> g[a] < g[b]).
  { intros. apply (OrderPM_Co1 _ _ (-a)%r) in H30; auto with real.
    rewrite Minus_P1 in H30; auto with real.
    apply H27 in H30; [ |apply Rat_P1a; auto; apply Rat_P3; auto].
    assert (∀ x, x ∈ Q -> g[x] ∈ Q').
    { intros. rewrite <-H19 in H31.
      apply Property_Value,Property_ran in H31; auto. }
    assert (g[(b - a)%r] = g[b] - g[a]).
    { pose proof H28. apply Rat_P3 in H32 as [H32 _].
      apply (H26 b) in H32 as [H32 _]; auto.
      rewrite PlusMult_Co3 in H32; auto with real.
      assert ((-(1)) ∈ Q)%r. { apply Rat_P3; auto with real. }
      pose proof H33. apply (H26 _ a) in H33 as [_]; auto.
      assert (g[1] + g[(-(1))%r] = 0').
      { apply (H26 1) in H34 as [H34 _]; auto with real.
        rewrite Minus_P1,H24 in H34; auto. }
      rewrite H25 in H35. apply Plus_Co3' in H35; auto with real'.
      rewrite Plus_P4',Plus_P1' in H35; auto with real'.
      rewrite H35,<-PlusMult_Co3' in H33; auto with real'.
      rewrite ReqR, ReqR' in *.
      rewrite H33,<-PlusMult_Co3 in H32; auto with real. eauto. }
    rewrite H32 in H30. apply (OrderPM_Co1' _ _ g[a]) in H30;
    auto with real'. rewrite Plus_P4',Plus_P1',<-Plus_P3',
    (Plus_P4' (-(g[a]))),Minus_P1',Plus_P1' in H30; auto with real'. }
  eauto 10.
Qed.

Open Scope R1_scope.

Lemma UniqueT5_Lemma5a : ∀ a b c, a ∈ Q -> b ∈ R -> c ∈ R
  -> 0 < a -> 0 < b -> 0 < c -> a < (b + c)
  -> ∃ a1 a2, a1 ∈ Q /\ a2 ∈ Q /\ 0 < a1 /\ a1 < b
    /\ 0 < a2 /\ a2 < c /\ a1 + a2 = a.
Proof.
  intros. assert ((a - c) < b).
  { apply (OrderPM_Co1 _ _ (-c)) in H5; auto with real.
    rewrite <-Plus_P3,Minus_P1,Plus_P1 in H5; auto with real. }
  assert (∃ a1, a1 ∈ Q /\ 0 < a1 /\ (a - c) < a1 /\ a1 < b /\ a1 < a)
    as [a1[H7[H8[H9[]]]]].
  { pose proof zero_in_R. pose proof H. apply Q_Subset_R in H8.
    apply (Order_Co1 _ (a - c)) in H7 as []; auto with real;
    apply (Order_Co1 b) in H8 as []; auto.
    - apply Arch_P9 in H6 as [a1[H6[]]]; auto with real.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto with real.
      apply (Order_Co2 _ (a - c)); auto with real; destruct H7; auto.
      apply (Order_Co2 _ b); auto with real; destruct H8; auto.
    - assert (a - c < a).
      { apply (OrderPM_Co1 _ _ a) in H4; auto with real.
        rewrite Plus_P4,Plus_P1,Plus_P4 in H4; auto with real.
        apply (OrderPM_Co1 _ _ (-c)) in H4; auto with real.
        rewrite <-Plus_P3,Minus_P1,Plus_P1 in H4; auto with real. }
      apply Arch_P9 in H9 as [a1[H9[]]]; auto with real.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto with real.
      apply (Order_Co2 _ (a - c)); auto with real; destruct H7; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (Order_Co2 _ a); auto with real; destruct H8; auto.
    - apply Arch_P9 in H3 as [a1[H3[]]]; auto with real.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto with real.
      apply (Order_Co2 _ 0); auto with real. right. split; auto.
      repeat destruct H7; auto.
      apply (Order_Co2 _ b); auto with real; destruct H8; auto.
    - apply Arch_P9 in H2 as [a1[H2[]]]; auto with real.
      exists a1. split; [ |split; [ |split; [ |split]]]; auto with real.
      apply (Order_Co2 _ 0); auto with real. right. split; auto.
      repeat destruct H7; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (Order_Co2 _ a); auto with real; destruct H8; auto. }
  apply (OrderPM_Co1 _ _ c) in H9; auto with real.
  rewrite <-Plus_P3,(Plus_P4 (-c)),Minus_P1,Plus_P1 in H9;
  auto with real. apply (OrderPM_Co1 _ _ (-a1)) in H9; auto with real.
  rewrite (Plus_P4 a1),<-Plus_P3,Minus_P1,Plus_P1 in H9; auto with real.
  exists a1,(a - a1). split; auto. split. apply Rat_P1a; auto.
  apply Rat_P3; auto. split; [ |split; [ |split; [ |split]]]; auto.
  apply (OrderPM_Co1 _ _ (-a1)) in H11; auto with real.
  rewrite Minus_P1 in H11; auto with real. rewrite Plus_P3,
  (Plus_P4 a1),<-Plus_P3,Minus_P1,Plus_P1; auto with real.
Qed.

Open Scope R2_scope.

Lemma UniqueT5_Lemma5b : ∀ a b c, a ∈ R' -> b ∈ R' -> c ∈ R'
  -> 0' < a -> 0' < b -> 0' < c -> a < (b + c)
  -> ∃ a1 a2, a1 ∈ R' /\ a2 ∈ R' /\ 0' < a1 /\ a1 < b
    /\ 0' < a2 /\ a2 < c /\ a1 + a2 = a.
Proof.
  intros. assert ((a - c) < b).
  { apply (OrderPM_Co1' _ _ (-c)) in H5; auto with real'.
    rewrite <-Plus_P3',Minus_P1',Plus_P1' in H5; auto with real'. }
  assert (∃ a1, a1 ∈ R' /\ 0' < a1 /\ (a - c) < a1 /\ a1 < b /\ a1 < a)
    as [a1[H7[H8[H9[]]]]].
  { pose proof zero_in_R'. pose proof H.
    apply (Order_Co1' _ (a - c)) in H7 as []; auto with real';
    apply (Order_Co1' b) in H8 as []; auto.
    - apply Arch_P9' in H6 as [a1[H6[]]]; auto with real'. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto with real'.
      apply (Order_Co2' _ (a - c)); auto with real'; destruct H7; auto.
      apply (Order_Co2' _ b); auto with real'; destruct H8; auto.
    - assert (a - c < a).
      { apply (OrderPM_Co1' _ _ a) in H4; auto with real'.
        rewrite Plus_P4',Plus_P1',Plus_P4' in H4; auto with real'.
        apply (OrderPM_Co1' _ _ (-c)) in H4; auto with real'.
        rewrite <-Plus_P3',Minus_P1',Plus_P1' in H4; auto with real'. }
      apply Arch_P9' in H9 as [a1[H9[]]]; auto with real'. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto with real'.
      apply (Order_Co2' _ (a - c)); auto with real'; destruct H7; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (Order_Co2' _ a); auto with real'; destruct H8; auto.
    - apply Arch_P9' in H3 as [a1[H3[]]]; auto with real'. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto with real'.
      apply (Order_Co2' _ 0'); auto with real'. right. split; auto.
      repeat destruct H7; auto.
      apply (Order_Co2' _ b); auto with real'; destruct H8; auto.
    - apply Arch_P9' in H2 as [a1[H2[]]]; auto with real'. exists a1.
      split; [ |split; [ |split; [ |split]]]; auto with real'.
      apply (Order_Co2' _ 0'); auto with real'. right. split; auto.
      repeat destruct H7; auto.
      destruct H8; [ |rewrite H8; auto].
      apply (Order_Co2' _ a); auto with real'; destruct H8; auto. }
  apply (OrderPM_Co1' _ _ c) in H9; auto with real'.
  rewrite <-Plus_P3',(Plus_P4' (-c)),Minus_P1',Plus_P1' in H9;
  auto with real'. apply (OrderPM_Co1' _ _ (-a1)) in H9;
  auto with real'. rewrite (Plus_P4' a1),<-Plus_P3',Minus_P1',Plus_P1'
  in H9; auto with real'. exists a1,(a - a1). split; auto.
  split. auto with real'.
  split; [ |split; [ |split; [ |split]]]; auto.
  apply (OrderPM_Co1' _ _ (-a1)) in H11; auto with real'.
  rewrite Minus_P1' in H11; auto. rewrite Plus_P3',(Plus_P4' a1),
  <-Plus_P3',Minus_P1',Plus_P1'; auto with real'.
Qed.

Open Scope R1_scope.

Lemma UniqueT5_Lemma6a : ∀ a b c, a ∈ Q -> b ∈ R -> c ∈ R
  -> 0 < a -> 0 < b -> 0 < c -> a < (b · c)
  -> ∃ a1 a2, a1 ∈ Q /\ a2 ∈ Q /\ 0 < a1 /\ a1 < b
    /\ 0 < a2 /\ a2 < c /\ a1 · a2 = a.
Proof.
  intros. assert (c ∈ (R ~ [0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H6; eauto with real. rewrite H6 in H4.
    destruct H4; auto. }
  pose proof H6. apply Mult_inv1,MKT4' in H7 as [H7 _].
  pose proof H4. apply OrderPM_Co10 in H8; auto.
  assert ((a / c) < b).
  { apply (OrderPM_Co7a _ _ (c⁻)) in H5; auto with real.
    rewrite <-Mult_P3,Divide_P1,Mult_P1 in H5; auto. }
  assert (0 < (a / c)).
  { apply (OrderPM_Co7a _ _ (c⁻)) in H2; auto with real.
    rewrite <-Mult_P4,PlusMult_Co1 in H2; auto with real. }
  assert (∃ a1, a1 ∈ Q /\ 0 < a1 /\ (a / c) < a1 /\ a1 < b)
    as [a1[H11[H12[]]]].
  { apply Arch_P9 in H9 as [a1[H9[]]]; auto with real. exists a1.
    split; [ |split; [ |split]]; auto with real.
    apply (Order_Co2 _ (a / c)); auto with real; destruct H11; auto. }
  assert (a1 ∈ (R ~ [0])).
  { apply MKT4'; split; auto with real. apply AxiomII; split; eauto.
    intro. apply MKT41 in H15; eauto with real. rewrite H15 in H12.
    destruct H12; auto. }
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  pose proof H15. apply Mult_inv1,MKT4' in H16 as [H16 _].
  pose proof H12. apply OrderPM_Co10 in H17; auto.
  exists a1,(a / a1). split; auto. split. apply Rat_P1b; auto.
  apply Rat_P7; auto. apply MKT4'; split; auto.
  apply MKT4' in H15; tauto. split; [ |split; [ |split; [ |split]]];
  auto. rewrite ReqR, ReqR' in *.
  apply (OrderPM_Co7a _ _ c) in H13; auto with real.
  rewrite Mult_P4,Mult_P3,(Mult_P4 c),<-Mult_P3,
  Divide_P1,Mult_P1,Mult_P4 in H13; auto with real.
  apply (OrderPM_Co7a _ _ (a1⁻)) in H13; auto with real.
  rewrite <-Mult_P3,Divide_P1,Mult_P1 in H13; auto.
  rewrite Mult_P4,<-Mult_P3,(Mult_P4 _ a1),Divide_P1,Mult_P1;
  auto with real.
Qed.

Open Scope R2_scope.

Lemma UniqueT5_Lemma6b : ∀ a b c, a ∈ R' -> b ∈ R' -> c ∈ R'
  -> 0' < a -> 0' < b -> 0' < c -> a < (b · c)
  -> ∃ a1 a2, a1 ∈ R' /\ a2 ∈ R' /\ 0' < a1 /\ a1 < b
    /\ 0' < a2 /\ a2 < c /\ a1 · a2 = a.
Proof.
  intros. assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (c ∈ (R' ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H6; eauto with real'. rewrite H6 in H4.
    destruct H4; auto. }
  pose proof H6. apply Mult_inv1',MKT4' in H7 as [H7 _].
  pose proof H4. apply OrderPM_Co10' in H8; auto.
  assert ((a / c) < b).
  { apply (OrderPM_Co7a' _ _ (c⁻)) in H5; auto with real'.
    rewrite <-Mult_P3',Divide_P1',Mult_P1' in H5; auto. }
  assert (0' < (a / c)).
  { apply (OrderPM_Co7a' _ _ (c⁻)) in H2; auto with real'.
    rewrite <-Mult_P4',PlusMult_Co1' in H2; auto with real'. }
  assert (∃ a1, a1 ∈ R' /\ 0' < a1 /\ (a / c) < a1 /\ a1 < b)
    as [a1[H11[H12[]]]].
  { apply Arch_P9' in H9 as [a1[H9[]]]; auto with real'. exists a1.
    split; [ |split; [ |split]]; auto with real'.
    apply (Order_Co2' _ (a / c)); auto with real'; destruct H11; auto. }
  assert (a1 ∈ (R' ~ [0'])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H15; eauto with real'. rewrite H15 in H12.
    destruct H12; auto. }
  pose proof H15. apply Mult_inv1',MKT4' in H16 as [H16 _].
  pose proof H12. apply OrderPM_Co10' in H17; auto.
  exists a1,(a / a1). split; auto. split. auto with real'.
  split; [ |split; [ |split; [ |split]]]; auto.
  rewrite ReqR, ReqR' in *.
  apply (OrderPM_Co7a' _ _ c) in H13;
  auto with real'. rewrite Mult_P4',Mult_P3',(Mult_P4' c),<-Mult_P3',
  Divide_P1',Mult_P1',Mult_P4' in H13; auto with real'.
  apply (OrderPM_Co7a' _ _ (a1⁻)) in H13; auto with real'.
  rewrite <-Mult_P3',Divide_P1',Mult_P1' in H13; auto.
  rewrite Mult_P4',<-Mult_P3',(Mult_P4' _ a1),Divide_P1',Mult_P1';
  auto with real'.
Qed.


Lemma UniqueT5_Lemma7 : ∃ f, Function f
  /\ dom(f) = \{ λ u, u ∈ R /\ (0 < u)%r \} /\ ran(f) ⊂ R'
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m + n)%r] = f[m] + f[n])
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m · n)%r] = f[m] · f[n])
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> (m < n)%r
    -> f[(n - m)%r] = f[n] - f[m]) /\ f[1] = 1'.
Proof.
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (QeqQ: (@Real_Axioms.Q R1) = Q) by auto.
  assert (QeqQ': (@Real_Axioms.Q R2) = Q') by auto.
  assert (NeqN: (@Real_Axioms.N R1) = N) by auto.
  assert (NeqN': (@Real_Axioms.N R2) = N') by auto.
  assert (ZeqZ: (@Real_Axioms.Z R1) = Z) by auto.
  assert (ZeqZ': (@Real_Axioms.Z R2) = Z') by auto.
  destruct UniqueT5_Lemma4 as [f[H[H0[H1[H2[H3[]]]]]]].
  set (A r := \{ λ u, ∃ x, x ∈ \{ λ v, v ∈ Q /\ (0 < v)%r
    /\ (v < r)%r \} /\ u = f[x] \}).
  assert (∀ r, (A r) ⊂ R') as Ha.
  { unfold Included; intros. apply AxiomII in H6 as [_[x[]]].
    apply AxiomII in H6 as [_[H6[]]]. rewrite <-H0 in H6.
    apply Property_Value,Property_ran in H6; auto.
    rewrite H7; auto with real'. }
  assert (∀ r, r ∈ Q -> f[r] ∈ R') as Hf.
  { intros. rewrite <-H0 in H6.
    apply Property_Value,Property_ran in H6; auto with real'. }
  set (g := \{\ λ u v, u ∈ R /\ (0 < u)%r /\ Sup1' (A u) v \}\).
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H6 as [_[_[_]]],H7 as [_[_[_]]].
    apply Sup_Corollary' in H6,H7. unfold Sup2' in H6,H7.
    eapply Min_Corollary'; eauto. }
  assert (dom(g) = \{ λ u, u ∈ R /\ (0 < u)%r \}).
  { apply AxiomI; split; intros. apply AxiomII in H7 as [_[]].
    apply AxiomII' in H7 as [_[H7[]]]. apply AxiomII; split; eauto.
    assert (exists ! y, Sup1' (A z) y) as [y[H8 _]].
    { apply SupT'; auto. apply NEexE. apply AxiomII in H7 as [_[]].
      apply Arch_P9 in H8 as [q[H8[]]]; auto with real. exists f[q].
      pose proof H8. rewrite QeqQ, QeqQ' in *. rewrite <-H0 in H11.
      apply Property_Value,Property_ran in H11; auto.
      apply AxiomII; split; eauto. exists q. split; auto.
      apply AxiomII; split; eauto. apply AxiomII in H7 as [_[]].
      pose proof H7. apply Arch_P10 in H9 as [m[[H9[_]]_]].
      apply (Int_P1a m 1),Z_Subset_Q in H9; auto with real.
      pose proof H9. rewrite QeqQ, QeqQ' in *. rewrite <-H0 in H11.
      apply Property_Value,Property_ran in H11; auto.
      exists f[(m + 1)%r]. repeat split; auto with real'. intros.
      apply AxiomII in H12 as [_[x0[]]].
      apply AxiomII in H12 as [_[H12[]]].
      assert (x0 < m + 1)%r.
      { apply (Order_Co2 _ z); auto with real; destruct H10; auto. }
      rewrite H13. apply H5 in H16 as []; auto. }
    apply AxiomII; split; eauto. exists y. apply AxiomII'; split.
    destruct H8 as [[_[]]]. apply MKT49a; eauto.
    apply AxiomII in H7 as [_[]]; auto. }
  assert (ran(g) ⊂ R').
  { unfold Included; intros. apply Einr in H8 as [x[]]; auto.
    apply Property_Value,AxiomII' in H8 as [_[_[]]]; auto.
    destruct H10 as [[_[]]]. rewrite H9; auto. }
  assert (∀ m, m ∈ dom(g) -> g[m] ∈ R').
  { intros. apply Property_Value,Property_ran in H9; auto. }
  assert (dom(g) ⊂ R).
  { unfold Included; intros. rewrite H7 in H10.
    apply AxiomII in H10; tauto. }
  assert (∀ m, m ∈ dom(g) -> 0' < g[m]).
  { intros. apply Property_Value,AxiomII' in H11 as [_[H11[]]]; auto.
    destruct H13 as [[_[]]_]. apply Arch_P9 in H12 as [x[H12[]]];
    auto with real. assert (f[x] ∈ (A m)).
    { apply AxiomII; split; [ |exists x]. rewrite QeqQ, QeqQ' in *.
      rewrite <-H0 in H12.
      apply MKT69b in H12; eauto. split; auto.
      apply AxiomII; split; eauto. }
    pose proof H17. apply H14 in H18. apply H5 in H15; auto.
    rewrite H2 in H15. apply (Order_Co2' _ f[x]); auto with real'.
    apply Z_Subset_Q. repeat (apply MKT4; right).
    apply MKT41; eauto with real. }
  assert (∀ m, m ∈ dom(g) -> Sup1' (A m) g[m]).
  { intros. apply Property_Value,AxiomII' in H12 as [_[_[]]]; auto. }
  assert (∀ a b, a ∈ Q -> b ∈ R -> (0 < a)%r -> (0 < b)%r
    -> (a < b)%r -> f[a] ≤ g[b]) as Hb.
  { intros. pose proof H13. rewrite <-H0 in H18.
    apply Property_Value,Property_ran in H18; auto.
    assert (f[a] ∈ (A b)).
    { apply AxiomII; split; eauto. exists a. split; auto.
      apply AxiomII; split; eauto. }
    assert (b ∈ dom(g)).
    { rewrite H7. apply AxiomII; split; eauto. }
    apply H12 in H20 as [[_[]]]; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g)
    -> g[(m + n)%r] = g[m] + g[n]).
  { intros. assert ((m + n)%r ∈ dom(g)).
    { rewrite H7. apply AxiomII; split; [exists R|split].
      apply H10 in H13, H14; autoR. apply H10 in H13, H14; autoR. 
      rewrite H7 in H13,H14.
      apply AxiomII in H13 as [_[]],H14 as [_[]].
      replace 0 with (0 + 0)%r. apply OrderPM_Co4; auto with real.
      destruct H15; auto. rewrite Plus_P1; auto with real. }
    assert (g[(m + n)%r] ∈ R'); auto.
    assert ((g[m] + g[n]) ∈ R'). auto with real'.
    pose proof H17. apply (Order_Co1' g[(m + n)%r]) in H18
    as [H18|[]]; auto.
    - pose proof H18. apply UniqueT5_Lemma5b in H19
      as [a1[a2[H19[H20[H21[H22[H23[]]]]]]]]; auto.
      pose proof H13; pose proof H14.
      apply H12 in H26 as [[_[_]]],H27 as [[_[_]]].
      apply H28 in H22 as [q1[]]; auto.
      apply AxiomII in H22 as [_[x1[]]].
      apply AxiomII in H22 as [_[H22[]]].
      apply H29 in H24 as [q2[]]; auto.
      apply AxiomII in H24 as [_[x2[]]].
      apply AxiomII in H24 as [_[H24[]]].
      assert (x1 + x2 < m + n)%r.
      { apply OrderPM_Co4; auto with real. destruct H33; auto. }
      assert (0 + 0 < x1 + x2)%r.
      { apply OrderPM_Co4; auto with real. destruct H32; auto. }
      rewrite Plus_P1 in H39; auto with real.
      apply Hb in H38; auto with real.
      assert (f[(x1 + x2)%r] = f[x1] + f[x2]). { apply H4; auto. }
      rewrite H40,<-H31,<-H35,<-H25 in H38.
      assert (a1 + a2 < q1 + q2) as [].
      { apply OrderPM_Co4'; auto;
        [rewrite H31|rewrite H35|destruct H30]; auto. }
      elim H42. apply Leq_P2'; auto with real'.
      rewrite H31,H35. apply Plus_close'; auto.
      rewrite H7 in H15. apply AxiomII in H15; tauto.
    - pose proof H15. apply H12 in H19 as [[_[_]]].
      pose proof H18. apply H20 in H21 as [q[]]; auto.
      apply AxiomII in H21 as [_[x[]]]. apply AxiomII in H21
      as [_[H21[]]]. pose proof H13; pose proof H14.
      rewrite H7 in H26,H27. apply AxiomII in H26 as [_[_]],
      H27 as [_[_]]. apply UniqueT5_Lemma5a in H25
      as [x1[x2[H25[H28[H29[H30[H31[]]]]]]]]; auto with real.
      apply Hb in H30,H32; auto.
      assert (f[x1] + f[x2] ≤ g[m] + g[n]).
      { apply OrderPM_Co3'; auto. }
      assert (f[(x1 + x2)%r] = f[x1] + f[x2]). { apply H4; auto. }
      rewrite <-H35,H33,<-H23 in H34. destruct H22. elim H36.
      apply Leq_P2'; auto. rewrite H23; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g)
    -> g[(m · n)%r] = g[m] · g[n]).
  { intros. assert ((m · n)%r ∈ dom(g)).
    { rewrite H7. apply AxiomII; split; [exists R|split].
      apply H10 in H14, H15; autoR. apply H10 in H14, H15; autoR.
      rewrite H7 in H14,H15.
      apply AxiomII in H14 as [_[]],H15 as [_[]].
      apply OrderPM_Co5; auto. }
    assert (g[(m · n)%r] ∈ R'); auto.
    assert ((g[m] · g[n]) ∈ R'). auto with real'.
    pose proof H18. apply (Order_Co1' g[(m · n)%r]) in H19
    as [H19|[]]; auto.
    - apply UniqueT5_Lemma6b in H19
      as [a1[a2[H19[H20[H21[H22[H23[]]]]]]]]; auto.
      pose proof H14; pose proof H15.
      apply H12 in H26 as [[_[_]]],H27 as [[_[_]]].
      apply H28 in H22 as [q1[]]; auto.
      apply AxiomII in H22 as [_[x1[]]].
      apply AxiomII in H22 as [_[H22[]]].
      apply H29 in H24 as [q2[]]; auto.
      apply AxiomII in H24 as [_[x2[]]].
      apply AxiomII in H24 as [_[H24[]]].
      assert (0 < m /\ 0 < n)%r as [].
      { rewrite H7 in H14,H15.
        split; [apply AxiomII in H14|apply AxiomII in H15]; tauto. }
      assert (x1 · x2 < m · n)%r.
      { apply (OrderPM_Co7a _ _ x2) in H33; auto with real.
        apply (OrderPM_Co7a _ _ m) in H37; auto with real.
        rewrite Mult_P4,(Mult_P4 n) in H37; auto with real.
        apply (Order_Co2 _ (m · x2)%r); auto with real.
        destruct H33; auto. }
      apply Hb in H40; auto with real; try apply OrderPM_Co5;
      auto with real.
      assert (f[(x1 · x2)%r] = f[x1] · f[x2]). { apply H4; auto. }
      rewrite H41,<-H31,<-H35,<-H25 in H40.
      assert (a1 · a2 < q1 · q2) as [].
      { apply (OrderPM_Co7a' _ _ a2) in H30; auto;
        [ |rewrite H31; auto].
        apply (OrderPM_Co7a' _ _ q1) in H34; auto;
        try rewrite H31; try rewrite H35; auto.
        rewrite Mult_P4',(Mult_P4' q2) in H34; auto;
        try rewrite H31; try rewrite H35; auto.
        rewrite <-H31,<-H35. apply (Order_Co2' _ (q1 · a2));
        try apply Mult_close'; destruct H34; auto;
        try rewrite H31; try rewrite H35; auto.
        rewrite <-H2. apply H5; auto. apply Z_Subset_Q.
        repeat (apply MKT4; right). apply MKT41; eauto with real. }
      elim H43. apply Leq_P2'; auto with real'.
      apply Mult_close'; [rewrite H31|rewrite H35]; auto.
    - pose proof H16. apply H12 in H20 as [[_[_]]].
      pose proof H19. apply H21 in H22 as [q[]]; auto.
      apply AxiomII in H22 as [_[x[]]]. apply AxiomII in H22
      as [_[H22[]]]. pose proof H14; pose proof H15.
      rewrite H7 in H27,H28. apply AxiomII in H27 as [_[_]],
      H28 as [_[_]]. apply UniqueT5_Lemma6a in H26
      as [x1[x2[H26[H29[H30[H31[H32[]]]]]]]]; auto with real.
      apply Hb in H31,H33; auto.
      assert (f[x1] · f[x2] ≤ g[m] · g[n]).
      { apply (OrderPM_Co7b' _ _ f[x2]) in H31; auto.
        apply (OrderPM_Co7b' _ _ g[m]) in H33; auto.
        rewrite Mult_P4',(Mult_P4' g[n]) in H33; auto.
        apply (Leq_P3' _ (g[m] · f[x2])); auto with real'.
        apply H11; auto. apply H5 in H32 as []; auto.
        rewrite <-H2; auto. apply Z_Subset_Q.
        repeat (apply MKT4; right). apply MKT41; eauto with real. }
      assert (f[(x1 · x2)%r] = f[x1] · f[x2]). { apply H4; auto. }
      rewrite <-H36,H34,<-H24 in H35. destruct H23. elim H37.
      apply Leq_P2'; auto. rewrite H24; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g) -> (m < n)%r
    -> g[(n - m)%r] = g[n] - g[m]).
  { intros. assert ((n - m)%r ∈ dom(g)).
    { rewrite H7 in *. apply AxiomII in H15 as [_[]],H16 as [_[]].
      apply AxiomII; split; [ |split]. exists R; autoR. autoR.
      apply (OrderPM_Co1 _ _ (-m)%r) in H17; auto with real.
      rewrite Minus_P1 in H17; auto. }
    assert (g[(n - m + m)%r] = g[(n - m)%r] + g[m]).
    { apply H13; auto. }
    rewrite <-Plus_P3,(Plus_P4 (-m)%r),Minus_P1,Plus_P1 in H19;
    auto with real. rewrite H19,<-Plus_P3',Minus_P1',Plus_P1';
    auto with real'. }
  assert (g[1] = 1').
  { assert (1 ∈ dom(g)).
    { rewrite H7; apply AxiomII; split; eauto with real. }
    assert (g[(1 · 1)%r] = g[1] · g[1]). { apply H14; auto. }
    assert (g[1] ∈ (R' ~ [0'])).
    { apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. apply MKT41 in H18; eauto with real'.
      apply H11 in H16 as []; auto. }
    rewrite Mult_P1 in H17; auto with real. symmetry in H17.
    apply Mult_Co3' in H17; auto.
    rewrite Divide_P1' in H17; auto. }
  exists g. split; auto. split; auto.
Qed.

Lemma UniqueT5_Lemma8 : ∃ f, Function f
  /\ dom(f) = R /\ ran(f) ⊂ R' /\ ran(f) <> [0']
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m + n)%r] = f[m] + f[n])
  /\ (∀ m n, m ∈ dom(f) -> n ∈ dom(f) -> f[(m · n)%r] = f[m] · f[n]).
Proof.
  destruct UniqueT5_Lemma7 as [f[H[H0[H1[H2[H3[]]]]]]].
  set (g := \{\ λ u v, u ∈ R /\ (((0 < u)%r /\ v = f[u])
    \/ (u = 0 /\ v = 0') \/ ((u < 0)%r /\ v = -f[(-u)%r])) \}\).
  assert (∀ m, m ∈ R -> (0 < m)%r -> f[m] ∈ R') as Hf.
  { intros. apply H1,(@ Property_ran m),Property_Value; auto.
    rewrite H0. apply AxiomII; split; eauto. }
  assert (∀ m, m ∈ R -> (m < 0)%r -> (0 < -m)%r) as Hb.
  { intros. apply (OrderPM_Co1 _ _ (-m)%r) in H7; auto with real.
    rewrite Minus_P1,Plus_P4,Plus_P1 in H7; auto with real. }
  assert (Function g).
  { split; unfold Relation; intros.
    apply AxiomII in H6 as [_[x[y[]]]]; eauto.
    apply AxiomII' in H6 as [_[H6[[]|[[]|[]]]]],
    H7 as [_[H7[[]|[[]|[]]]]]; try rewrite H9,H11; auto;
    try (rewrite H8 in H10; destruct H10; contradiction);
    try (destruct H8,H10; elim H12; apply Leq_P2; auto with real).
    destruct H8. elim H12. auto. rewrite H10 in *. destruct H8.
    tauto. }
  assert (dom(g) = R).
  { apply AxiomI; split; intros.
    apply Property_Value,AxiomII' in H7 as [_[]]; auto.
    pose proof H7. apply (Order_Co1 0) in H8 as [H8|[]];
    auto with real; apply AxiomII; split; eauto.
    - exists f[z]. apply AxiomII'; split; auto. apply MKT49a; eauto.
    - exists (-f[(-z)%r]). apply AxiomII'; split; auto.
      apply MKT49a; eauto. exists R'.
      apply Plus_neg1a',Hf; auto with real.
    - exists 0'. apply AxiomII'; split; auto.
      apply MKT49a; eauto with real'. }
  assert (ran(g) ⊂ R').
  { unfold Included; intros. apply Einr in H8 as [x[]]; auto.
    apply Property_Value,AxiomII' in H8 as [_[H8[[]|[[]|[]]]]]; auto;
    rewrite H9,H11; auto with real'. }
  assert (ReqR: (@Real_Axioms.R R1) = R) by auto.
  assert (ReqR': (@Real_Axioms.R R2) = R') by auto.
  assert (g[0] = 0').
  { pose proof zero_in_R. rewrite ReqR, ReqR' in *. rewrite <-H7 in H9.
    apply Property_Value,AxiomII' in H9 as [_[H9[[]|[[]|[]]]]]; auto;
    destruct H10; contradiction. }
  assert (∀ m, m ∈ R -> (0 < m)%r -> g[m] = f[m]).
  { intros. rewrite <-H7 in H10.
    apply Property_Value,AxiomII' in H10 as [_[H10[[]|[[]|[]]]]]; auto.
    rewrite H12 in H11. destruct H11; contradiction.
    destruct H11,H12. elim H14. apply Leq_P2; auto with real. }
  assert (∀ m, m ∈ R -> (m < 0)%r -> g[m] = -f[(-m)%r]).
  { intros. rewrite <-H7 in H11.
    apply Property_Value,AxiomII' in H11 as [_[H11[[]|[[]|[]]]]]; auto.
    destruct H12,H13. elim H15. apply Leq_P2; auto with real.
    rewrite H13 in H12. destruct H12; contradiction. }
  assert (g[1] = 1'). { rewrite H10; auto with real. }
  assert (ran(g) <> [0']).
  { assert (1' ∈ ran(g)).
    { rewrite <-H12. apply (@ Property_ran 1),Property_Value; auto.
      rewrite H7; auto with real. }
    intro. rewrite H14 in H13. apply MKT41 in H13; eauto with real'.
    destruct OrderPM_Co9'; auto. }
  assert (∀ m, m ∈ R -> g[m] ∈ R') as Hg.
  { intros. apply H8,(@ Property_ran m),Property_Value; auto.
    rewrite H7; auto. }
  assert (∀ m n, m ∈ R -> n ∈ R -> (0 < m)%r -> (n < 0)%r
    -> g[(m + n)%r] = g[m] + g[n] /\ g[(m · n)%r] = g[m] · g[n]).
  { intros. rewrite (H10 m),(H11 n); auto.
    assert (m ∈ dom(f) /\ (-n)%r ∈ dom(f)) as [].
    { rewrite H0. split; apply AxiomII; split; eauto with real. }
    pose proof zero_in_R. apply (Order_Co1 (m + n)%r) in H20
    as [H20|[]]; auto with real.
    - rewrite H11; auto with real. split. rewrite PlusMult_Co3,
      Mult_P4,Mult_P5,Mult_P4,<-PlusMult_Co3,Mult_P4,<-PlusMult_Co3,
      Plus_P4,H4,PlusMult_Co3',Mult_P4',Mult_P5',Mult_P4',
      <-PlusMult_Co3',Mult_P4',PlusMult_Co4',Plus_P4';
      auto with real real'.
      apply (OrderPM_Co1 _ _ (-n)%r) in H20; auto with real.
      rewrite <-Plus_P3,Minus_P1,Plus_P1,Plus_P4,Plus_P1 in H20;
      auto with real.
      rewrite H11; auto with real. rewrite PlusMult_Co3,Mult_P3,
      (Mult_P4 _ m),<-Mult_P3,<-PlusMult_Co3,H3; auto with real.
      rewrite PlusMult_Co3',Mult_P3',(Mult_P4' _ f[m]),<-Mult_P3',
      <-PlusMult_Co3'; auto with real real'.
      rewrite Mult_P4; auto. apply OrderPM_Co6; auto.
    - rewrite H10; auto with real. split. pattern n at 1.
      rewrite <-(PlusMult_Co4 n),<-PlusMult_Co3,H4; auto with real.
      apply (OrderPM_Co1 _ _ (-n)%r) in H20; auto with real.
      rewrite <-Plus_P3,Minus_P1,Plus_P4,Plus_P1,Plus_P1 in H20;
      auto with real.
      rewrite H11,PlusMult_Co3,Mult_P3,(Mult_P4 _ m),<-Mult_P3,
      <-PlusMult_Co3,H3,PlusMult_Co3',Mult_P3',(Mult_P4' _ f[m]),
      <-Mult_P3',<-PlusMult_Co3'; auto with real real'.
      rewrite Mult_P4; auto. apply OrderPM_Co6; auto.
    - rewrite H20. rewrite Plus_P4 in H20; auto.
      apply Plus_Co3 in H20; auto with real.
      rewrite Plus_P4,Plus_P1 in H20; auto with real. split.
      rewrite ReqR, ReqR' in *.
      rewrite <-H20,Minus_P1'; auto. rewrite ReqR, ReqR' in *.
      rewrite H11,PlusMult_Co3,Mult_P3,(Mult_P4 _ m),<-Mult_P3,
      <-PlusMult_Co3,<-H20,H3,PlusMult_Co3',Mult_P3',
      <-PlusMult_Co3',Mult_P4'; auto with real real'.
      rewrite Mult_P4; auto. apply OrderPM_Co6; auto. }
  assert (∀ m n, m ∈ R -> n ∈ R -> (m < 0)%r -> (n < 0)%r
    -> g[(m + n)%r] = g[m] + g[n] /\ g[(m · n)%r] = g[m] · g[n]).
  { intros. rewrite (H11 m),(H11 n); auto.
    assert ((-m)%r ∈ dom(f) /\ (-n)%r ∈ dom(f)) as [].
    { rewrite H0. split; apply AxiomII; split; eauto with real. }
    assert (m + n < 0 + 0)%r.
    { apply OrderPM_Co4; auto with real. destruct H17; auto. }
    rewrite Plus_P1 in H21; auto with real. split.
    rewrite H11,PlusMult_Co3,Mult_P4,Mult_P5,Mult_P4,<-PlusMult_Co3,
    Mult_P4,<-PlusMult_Co3,H2,PlusMult_Co3',Mult_P4',Mult_P5',
    Mult_P4',<-PlusMult_Co3',Mult_P4',<-PlusMult_Co3';
    auto with real real'.
    assert (m · n = (-m) · (-n))%r.
    { rewrite ReqR, ReqR' in *.
      rewrite PlusMult_Co3,(PlusMult_Co3 n),Mult_P3,
      (Mult_P4 (-(1))%r),<-(Mult_P3 m),PlusMult_Co5,Mult_P1,
      Mult_P1; auto with real. } rewrite ReqR, ReqR' in *.
    rewrite H22. rewrite H10,H3,PlusMult_Co3',
    (PlusMult_Co3' f[(-n)%r]),Mult_P3',(Mult_P4' (-1')),
    <-(Mult_P3' f[(-m)%r]),PlusMult_Co5',Mult_P1',Mult_P1';
    auto with real real'.  }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g)
    -> g[(m + n)%r] = g[m] + g[n]).
  { intros. 
    apply Property_Value,AxiomII' in H16
    as [_[H16[[]|[[]|[]]]]],H17 as [_[H17[[]|[[]|[]]]]]; auto.
    rewrite H10. rewrite H19, H21; apply H2;
    rewrite H0; apply AxiomII; split autoR. autoR.
    replace 0 with (0 + 0)%r. apply OrderPM_Co4; auto with real.
    destruct H18; auto. autoR.
    rewrite H20,Plus_P1,H9,Plus_P1'; auto. apply H14; auto.
    rewrite H18,Plus_P4,Plus_P1,H9,Plus_P4',Plus_P1';
    auto with real real'.
    rewrite H19,H21,H18,H20,Plus_P1,H9,Plus_P1'; auto with real real'.
    rewrite H18,Plus_P4,Plus_P1,H9,Plus_P4',Plus_P1';
    auto with real real'.
    rewrite Plus_P4,Plus_P4'; auto. apply H14; auto.
    rewrite H20,Plus_P1,H9,Plus_P1'; auto.
    apply H15; auto. }
  assert (∀ m n, m ∈ dom(g) -> n ∈ dom(g)
    -> g[(m · n)%r] = g[m] · g[n]).
  { clear H16. intros. apply Property_Value,AxiomII' in H16
    as [_[H16[[]|[[]|[]]]]],H17 as [_[H17[[]|[[]|[]]]]]; auto.
    rewrite H10,H19,H21,H3; try (rewrite H0; apply AxiomII; split);
    eauto with real.
    rewrite H20,PlusMult_Co1,H9,PlusMult_Co1'; auto.
    apply H14; auto. rewrite H19,H18,Mult_P4,Mult_P4',
    PlusMult_Co1,PlusMult_Co1'; auto with real real'.
    rewrite H20,PlusMult_Co1,H9,PlusMult_Co1'; auto.
    rewrite H18,Mult_P4,PlusMult_Co1,H9,Mult_P4',PlusMult_Co1';
    auto with real real'.
    rewrite Mult_P4,Mult_P4'; auto. apply H14; auto.
    rewrite H20,PlusMult_Co1,H9,PlusMult_Co1'; auto.
    apply H15; auto. }
  exists g. split; auto.
Qed.

Definition reals_isomorphism := ∃ f, Function1_1 f /\ dom(f) = R /\ ran(f) = R'
    /\ (∀ x y, x ∈ R -> y ∈ R
    -> f[(x + y)%r] = (f[x] + f[y])%r'
    /\ f[(x · y)%r] = (f[x] · f[y])%r'
    /\ ((x ≤ y)%r <-> (f[x] ≤ f[y])%r')).

Theorem UniqueT5 : reals_isomorphism.
Proof.
  assert (H:True) by auto. unfold reals_isomorphism.
  intros. destruct UniqueT5_Lemma8 as [f[H0[H1[H2[H3[]]]]]].
  pose proof H0. apply UniqueT4 in H6 as [H6[H7[]]]; auto;
  [ |intros; split; [apply H4|apply H5]; rewrite H1; auto].
  exists f. split; auto. repeat split; auto;
  [apply H4|apply H5| ]; try rewrite H1; auto.
  assert (∀ r, r ∈ R -> f[r] ∈ R').
  { intros. rewrite <-H1 in H12.
    apply Property_Value,Property_ran in H12; auto. }
  intros. pose proof H10.
  apply (Order_Co1 y) in H14 as [H14|]; auto.
  assert (y ≤ x)%r. { destruct H14; auto. }
  apply H9 in H15; auto.
  assert (f[x] = f[y]). { apply Leq_P2'; auto. }
  apply f11inj in H16; try rewrite H1; auto.
  rewrite H16 in H14. destruct H14; contradiction.
  destruct H6; auto.
  destruct H14; [destruct H14|rewrite H14]; auto.
Qed.

End R_Uniqueness.
Print Assumptions UniqueT5.

















