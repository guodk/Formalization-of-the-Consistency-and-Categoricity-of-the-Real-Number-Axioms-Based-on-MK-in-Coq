Require Export MK_Foundation_Analysis.
Require Export Real_Axioms.
Definition R0 := {|
  R:=RC;
  fp := (\{\ λ u v, ∃ x y, x∈RC /\ y∈RC /\ u = [x, y] /\ (addR x)[y] = v \}\);
  zeroR := zero;
  fm := (\{\ λ u v, ∃ x y, x∈RC /\ y∈RC /\ u = [x, y] /\ (mulR x)[y] = v \}\);
  oneR := 1%RC;
  Leq := (\{\ λ u v, u∈RC /\ v∈RC /\ leR u v \}\);
|}.
Fact peqp : ∀ x y, x ∈ RC -> y ∈ RC -> (@fp R0)[[x, y]] = (addR x)[y].
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H1. apply H2. appA2G. apply AxiomII'. split; rxo.
    exists x, y. repeat split; auto. 
  - appA2G. intros. appA2H H2. apply AxiomII' in H3; deand.
    destruct H4 as [x1[y1[?[?[]]]]]. subst. apply MKT55 in H6; rxo.
    destruct H6. subst; auto.
Qed.

Fact meqm : ∀ x y, x ∈ RC -> y ∈ RC -> (@fm R0)[[x, y]] = (mulR x)[y].
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H1. apply H2. appA2G. apply AxiomII'. split; rxo.
    exists x, y. repeat split; auto.
  - appA2G. intros. appA2H H2. apply AxiomII' in H3; deand.
    destruct H4 as [x1[y1[?[?[]]]]]. subst. apply MKT55 in H6; rxo.
    destruct H6. subst; auto.
Qed.

Fact leql : ∀ x y, x ∈ RC -> y ∈ RC -> [x, y] ∈ (@Leq R0) <-> (leR x y).
Proof.
  intros; split; intros.
  - appA2H H1. destruct H2 as [x1[y1[?[?[]]]]]. apply MKT55 in H2; rxo.
    destruct H2; subst; auto.
  - appA2G. apply MKT49a; eauto. exists x, y. repeat split; auto.
Qed.

Definition upper_RC X := 
  \{ λ r, r ∈ RC /\ (∀r0 : Class,r0 ∈ X -> (r0 < r)%RC) \}.
Print divide.

Theorem RC_divide : ∀X, X ⊂ RC ->
             X <> Φ -> (∃ y, y∈ RC /\
             (∀x ,x ∈ X -> (x < y)%RC)) ->
             divide (Setminus RC (upper_RC X)) (upper_RC X).
Proof.
  intros. destruct H1 as [y []]. repeat split.
  - red. intros. appA2H H3. tauto.
  - red. intros. appA2H H3. tauto.
  - intro. assert (exists x, x ∈ X). apply NEexE; auto.
    destruct H4. assert (x∈(RC ~ upper_RC X)).
    { apply AxiomII; split. eauto. split; auto.
      appA2G. intro. appA2H H5. destruct H6. apply H7 in H4.
      assert (x = x). auto. CordR. } rewrite H3 in H5. eapply MKT16; eauto.
  - intro. assert (y∈(upper_RC X)). { appA2G. }
    rewrite H3 in H4. eapply MKT16; eauto.
  - red. intros. destruct (classic (a ∈ upper_RC X)); auto.
  - red. intros. assert ((b < a)%RC -> False).
    { intro. appA2H H4. destruct H6. appA2H H3.
      destruct H8. appA2H H9. destruct H10.
      apply AxiomII. split. eauto. split; auto.
      intros. pose proof H10. apply H in H10. apply H7 in H11.
      pose proof @T171 r0 b a.
      apply H12; auto. } appA2H H3. destruct H6. appA2H H7. pose proof H4.
      appA2H H9. destruct H10 as [? _].
      destruct (@T167 a b) as [?|[?|?]]; auto. rewrite H11 in H8. 
      contradiction. apply H5 in H11. contradiction.
Qed.

Program Instance RA0 : Real_axioms R0.
Obligation 1. apply EnRC. Qed.
Obligation 2.
  repeat split.
  - apply poisre.
  - intros. apply AxiomII' in H; apply AxiomII' in H0; deand.
    destruct H2 as [x1[y1[?[?[]]]]]. destruct H1 as [x2[y2[?[?[]]]]]. subst.
    apply MKT55 in H7; rxo. destruct H7; subst; auto.
  - apply AxiomI; split; intros.
    + appA2H H. destruct H0 as [y]. apply AxiomII' in H0; deand.
      destruct H1 as [x1[y1[?[?[]]]]]. subst. appA2G.
    + appA2H H. destruct H0 as [x1[y1[?[]]]]. subst. appA2G. exists ((addR x1)[y1]).
      apply AxiomII'. split; rxo. exists x1,y1. repeat split; auto.
  - red. intros. appA2H H. destruct H0. apply AxiomII' in H0; deand.
    destruct H1 as [x1[y1[?[?[]]]]]. subst. auto. Qed.
Obligation 3. auto. Qed.
Obligation 4. intros. rewrite peqp; auto. apply AddRpb; auto. Qed.
Obligation 5.
  intros. exists (-x)%RC. split; auto. rewrite peqp; auto. apply T179; auto. Qed.
Obligation 6.
  intros. repeat rewrite peqp; auto. symmetry. apply T186; auto. Qed.
Obligation 7.
  intros. repeat rewrite peqp; auto. apply T175; auto. Qed.
Obligation 8.
  repeat split.
  - apply poisre.
  - intros. apply AxiomII' in H; apply AxiomII' in H0; deand.
    destruct H2 as [x1[y1[?[?[]]]]]. destruct H1 as [x2[y2[?[?[]]]]]. subst.
    apply MKT55 in H7; rxo. destruct H7; subst; auto.
  - apply AxiomI; split; intros.
    + appA2H H. destruct H0 as [y]. apply AxiomII' in H0; deand.
      destruct H1 as [x1[y1[?[?[]]]]]. subst. appA2G.
    + appA2H H. destruct H0 as [x1[y1[?[]]]]. subst. appA2G. exists ((mulR x1)[y1]).
      apply AxiomII'. split; rxo. exists x1,y1. repeat split; auto.
  - red. intros. appA2H H. destruct H0. apply AxiomII' in H0; deand.
    destruct H1 as [x1[y1[?[?[]]]]]. subst. auto. Qed.
Obligation 9.
  appA2G. split; auto. appA2G. intro. apply MKT41 in H; rxo.
  assert (1%RC ∈ PRC). auto. assert(1%RC = (@oneR R0)). auto.
  rewrite H1 in H0. rewrite H in H0. assert(0%RC = (@zeroR R0)). auto.
  rewrite <- H2 in H0. npz. Qed.
Obligation 10.
  intros. rewrite meqm; auto. apply T195; auto. Qed.
Obligation 11.
  intros. exists (1/x)%RC. appA2H H. destruct H0. appA2H H1.
  assert (x <> 0%RC). { intro. elim H2. apply MKT41; auto. } split. appA2G.
  split; auto. appA2G. intro. apply MKT41 in H4; rxo. apply divR4' in H4; auto.
  assert (1%RC ∈ PRC). auto. rewrite H4 in H5; npz. rewrite meqm; auto.
  rewrite T194; auto. apply divREX; auto. Qed.
Obligation 12.
  intros. repeat rewrite meqm; auto. rewrite T199; auto. Qed.
Obligation 13.
  intros. repeat rewrite meqm; auto. rewrite T194; auto. Qed.
Obligation 14.
  intros. repeat rewrite peqp; repeat rewrite meqm; auto.
  rewrite T201'; auto. Qed.
Obligation 15.
  red. intros. appA2H H. destruct H0 as [x1[y1[?[?[]]]]]. subst. appA2G. Qed.
Obligation 16.
  intros. apply leql; auto. right; auto. Qed.
Obligation 17.
  intros. apply leql in H1,H2; auto. destruct H1; auto. pose proof (@legRf y x). MP.
  contradiction. Qed.
Obligation 18.
  intros. apply leql in H3,H2; auto. apply leql; auto. apply T173 with y; auto. Qed.
Obligation 19.
  intros. pose proof (@T167 x y). MP. destruct H1 as [?|[?|?]].
  left. apply leql; auto. right; auto. right. apply leql; auto. left; auto.
  left. apply leql; auto. left; auto. Qed.
Obligation 20.
  intros. apply leql in H2; auto. apply leql; repeat rewrite peqp; auto.
  apply T191; auto. right; auto. Qed.
Obligation 21.
  intros. apply leql in H1,H2; auto. rewrite meqm; auto. apply leql; auto.
  destruct H1,H2. left. apply T169; auto. rewrite <- H2. right. reqa1.
  rewrite <- H1. right. reqa1. rewrite <- H1. right. reqa1. Qed.
Obligation 22.
  intros. destruct (classic (X∩Y = Φ)) as [em|nem]. {
  pose proof T205a. pose proof RC_divide _ H H1.
  assert (divide (RC ~ upper_RC X) (upper_RC X)). {
    apply H5. assert (exists y, y ∈ Y). { apply NEexE; auto. }
    destruct H6 as [y ?]. exists y. split; auto.
    intros. destruct (@T167 x y); auto.
    - assert (x∈X ∩ Y). { appA2G. split; subst; auto. }
      rewrite em in H9. pose proof (@MKT16 x). destruct H10; auto.
    - destruct H8; auto. pose proof H3 _ _ H7 H6.
      apply leql in H9; auto. destruct H9; CordR. }
  apply H4 in H6. destruct H6 as [e []].
  exists e. split; auto. intros. destruct H7.
  pose proof @T167. assert (Hx: x ∈ RC). auto. assert (Hy: y∈RC); auto.
  pose proof H11 x e Hx H6.
  pose proof H11 e y H6 Hy.
  split.
  - apply leql; auto. destruct H12; auto. right; auto.
    destruct H12.
    + apply H10 in H12; auto. appA2H H12. destruct H14.
      apply H15 in H8; auto. assert (x=x); auto. CordR.
    + left; auto.
  - apply leql; auto. destruct H13; auto. right; auto.
    destruct H13. pose proof H13 as Hey.
    + apply H7 in H13; auto. appA2H H13. destruct H14.
      appA2H H15. destruct H16. apply AxiomII. split.
      eauto. split; auto. intros. pose proof H3 _ _ H16 H9.
      apply leql in H17; auto. assert ((r0 < y)%RC \/ (r0 = y)%RC).
      { auto. } destruct H18; auto.
      assert (y ∈ X ∩ Y). { appA2G. subst; auto. } rewrite em in H19.
      pose proof (@MKT16 y). contradiction.
    + left; auto. }
  assert (exists c, c ∈ X ∩ Y). { apply NEexE; auto. }
  destruct H4 as [c ?]. appA2H H4. destruct H5.
  exists c. split; auto.
Qed.

Require Import Real_uniqueness.
Print reals_isomorphism.
Theorem R0_uniqueness : forall (R1:Real_struct) (RA1:Real_axioms R1),
  reals_isomorphism R0 R1.
Proof.
  intros. apply UniqueT5; auto. apply RA0.
Qed.
Print Assumptions R0_uniqueness.




  