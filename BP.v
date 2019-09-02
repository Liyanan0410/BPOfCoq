Require Export List.
Require Export ListSet.
Require Export Coq.Init.Nat.
Require Export Coq.Bool.Bool.
Require Export Coq.Logic.Classical.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

(***************************************************************************)
(* 对Basic Paxos算法涉及到的对象全部进行抽象类型定义，并证明一些定理。                 *)
(***************************************************************************)
Inductive priest : Type :=
  | priestId : nat -> priest.


Inductive decree : Type :=
  | decreeId : nat -> decree.


Inductive number : Type :=
  | numberId : nat -> number.


Definition beq_priest (x1 x2 : priest) :=
  match x1, x2 with
  | priestId n1, priestId n2 => Nat.eqb n1 n2
  end.


Definition beq_decree (x1 x2 : decree) :=
  match x1, x2 with
  | decreeId n1, decreeId n2 => Nat.eqb n1 n2
  end.


Definition blt_decree (x1 x2 : decree) :=
  match x1, x2 with
  | decreeId n1, decreeId n2 => ltb n1 n2
  end.


Theorem beq_decree_true : forall d1 d2 : decree,
  beq_decree d1 d2 = true -> d1 = d2.
Proof.
  intros d1. destruct d1. intros d2. induction d2.
  generalize dependent n0. induction n.
  - intros n0. simpl. destruct n0.
    + intros. reflexivity.
    + intros. inversion H.
  - intros n0. simpl. destruct n0.
    + intros. inversion H.
    + intros H. simpl in IHn. apply IHn in H.
      inversion H. reflexivity.
Qed.


Theorem beq_decree_refl : forall d : decree,
  true = beq_decree d d.
Proof.
  intros d. destruct d. induction n.
  - reflexivity.
  - rewrite IHn. simpl. reflexivity.
Qed.


Theorem beq_decree_true_iff : forall d1 d2 : decree,
  beq_decree d1 d2 = true <-> d1 = d2.
Proof.
  split.
  - apply beq_decree_true.
  - intros. rewrite H. symmetry. apply beq_decree_refl.
Qed.


Definition beq_number (x1 x2 : number) :=
  match x1, x2 with
  | numberId n1, numberId n2 => Nat.eqb n1 n2
  end.


(* 小于判断 *)
Definition blt_number (x1 x2 : number) :=
  match x1, x2 with
  | numberId n1, numberId n2 => ltb n1 n2
  end.


Theorem beq_number_true : forall n1 n2 : number,
  beq_number n1 n2 = true -> n1 = n2.
Proof.
  intros n1. destruct n1. intros n2. induction n2.
  generalize dependent n0. induction n.
  - intros n0. simpl. destruct n0.
    + intros. reflexivity.
    + intros. inversion H.
  - intros n0. simpl. destruct n0.
    + intros. inversion H.
    + intros H. simpl in IHn. apply IHn in H.
      inversion H. reflexivity.
Qed.


Theorem beq_number_refl : forall num : number,
  true = beq_number num num.
Proof.
  intros num. destruct num. induction n.
  - reflexivity.
  - rewrite IHn. simpl. reflexivity.
Qed.


Theorem beq_number_true_iff : forall n1 n2 : number,
  beq_number n1 n2 = true <-> n1 = n2.
Proof.
  split.
  - apply beq_number_true.
  - intros. rewrite H. symmetry. apply beq_number_refl.
Qed.


Hypothesis Aeq_dec : forall x y:priest, {x = y} + {x <> y}.


(***************************************************************************)
(* Basic Paxos算法中，对Quorums的定义及其重要性质和引理的定义和证明。                *)
(***************************************************************************)
Variables Quorums : set (set priest).

Lemma DoublePredicate : forall Q1 Q2 : set priest, set_In Q1 Quorums -> set_In Q2 Quorums
  -> set_In Q1 Quorums /\ set_In Q2 Quorums.
Proof.
  intros. split. apply H. apply H0.
Qed.


Lemma DoublePredicateL : forall Q1 Q2 : set priest, set_In Q1 Quorums /\ set_In Q2 Quorums -> In Q1 Quorums.
Proof.
  intros. inversion H. apply H.
Qed.


Lemma DoublePredicateR : forall Q1 Q2 : set priest, set_In Q1 Quorums /\ set_In Q2 Quorums -> In Q2 Quorums.
Proof.
  intros. inversion H. apply H.
Qed.


Lemma empty_spec : forall x, ~(set_In x (empty_set priest)).
Proof.
  intros. unfold empty_set. unfold not.
  intros. inversion H.
Qed.


Lemma empty_spec_iff : forall x, set_In x (empty_set priest) <-> False.
Proof.
  intros. split.
  - apply empty_spec.
  - intros. inversion H.
Qed.


Lemma empty_spec_mem : forall Q , (exists x, set_mem Aeq_dec x Q = true) -> Q <> empty_set priest.
Proof.
  intros. inversion H. apply set_mem_correct1 in H0.
  unfold not. intros. rewrite H1 in H0.
  apply empty_spec_iff in H0. apply H0.
Qed.


Hypothesis QuorumsAssumption: forall Q1 Q2, In Q1 Quorums -> In Q2 Quorums ->
  set_inter Aeq_dec Q1 Q2 <> empty_set priest.


Hypothesis QuorumsAssumptionE: forall Q1 Q2 : set priest, In Q1 Quorums /\ In Q2 Quorums ->
  exists q, set_In q (set_inter Aeq_dec Q1 Q2).


Lemma QuorumNonEmptyAuxiliaryO : forall Q1 Q2, In Q1 Quorums /\ In Q2 Quorums ->
  Q1 <> empty_set priest /\ Q2 <> empty_set priest.
Proof.
  intros. apply  QuorumsAssumptionE in H. inversion H.
  apply set_inter_elim in H0. inversion H0. split.
  - apply empty_spec_mem. exists x.
    apply set_mem_correct2. apply H1.
  - apply empty_spec_mem. exists x.
    apply set_mem_correct2. apply H2.
Qed.


Lemma QuorumNonEmptyAuxiliaryT : forall Q1 Q2, In Q1 Quorums -> In Q2 Quorums ->
  Q1 <> empty_set priest /\ Q2 <> empty_set priest.
Proof.
  intros. specialize (DoublePredicate Q1 Q2).
  intros. apply H1 in H.
  - apply QuorumNonEmptyAuxiliaryO. apply H.
  - apply H0.
Qed.


Lemma QuorumNonEmpty : forall Q, In Q Quorums -> Q <> empty_set priest.
Proof.
  intros. specialize (QuorumNonEmptyAuxiliaryT Q Q).
  intros. apply H0 in H.
  - inversion H. apply H1. 
  - apply H.
Qed.

(***************************************************************************)
(* 对集合定性质的补充。                                                        *)
(***************************************************************************)
Definition subset (u v : set priest) := forall a, set_In a u -> set_In a v.


(* 修改nincl定义。*)
Inductive nincl (u v : set priest) : Prop :=
  nincl_cons : forall a, In a u -> ~ In a v -> nincl u v.
  

(* 修改sincl定义。*)
Definition sincl (u v : set priest) := subset u v /\ (exists a, In a v /\ ~In a u).


(* 增加Axiom_Extent及以下两个推论并证明推论。*)
Axiom Axiom_Extent : forall x y : set priest,
  x = y <-> (forall z, In z x <-> In z y).
  

Lemma Axiom_infer1 : forall x y : set priest,
  x <> y <-> ~(forall z, In z x <-> In z y).
Proof.
  intros. apply not_iff_compat. apply Axiom_Extent.
Qed.


Lemma Axiom_infer2 : forall x y : set priest,
  ~(forall z, In z x <-> In z y) -> (exists a, In a x /\ ~In a y) \/ (exists a, In a y /\ ~In a x).
Proof.
  intros. apply not_all_ex_not in H.  inversion H. unfold iff in H0. apply not_and_or in H0.  destruct H0.
  - apply imply_to_and in H0. left. exists x0. apply H0.
  - apply imply_to_and in H0. right. exists x0. apply H0.
Qed.


(* 将原有的setDecR假设去掉，增加了对应的引理并证明。*)
Lemma setDecR : forall u v : set priest, (exists a, In a v /\ ~In a u) -> u <> v.
Proof.
  intros. inversion H. destruct (list_eq_dec Aeq_dec u v).
  + destruct e. unfold not. intros. inversion H0. unfold not in H3. apply H3 in H2. apply H2.
  + apply n.
Qed.


Lemma setDecL : forall u v : set priest, (exists a, In a u /\ ~In a v) -> u <> v.
Proof.
  intros. inversion H. destruct (list_eq_dec Aeq_dec u v).
  + destruct e. destruct H0. eauto. 
  + apply n.
Qed.


(* 增加set_NotSubset引理并证明。*)
Lemma set_NotSubset : forall u v : set priest, (exists a, In a v /\ ~In a u) <-> ~ subset v u.
Proof.
  intros; split.
 - intros H1 H2. destruct H1. generalize (H2 x); intro H3. destruct H as [H H1].
   apply H3 in H. auto.
 - intro H. apply not_all_ex_not in H. destruct H. exists x. apply imply_to_and in H. auto.
Qed.


(* 将原有的setIntuition假设去掉，增加了对应的引理并证明。*)
Lemma setIntuitionL : forall u v , subset u v -> sincl u v \/ u = v.
Proof.
  intros. destruct (list_eq_dec Aeq_dec u v).
  - right. apply e.
  - left. apply Axiom_infer1 in n. apply Axiom_infer2 in n. unfold sincl. split.
    + apply H.
    + unfold subset in H. destruct n.
      { inversion H0. generalize (H x). intros. inversion H1.  apply H2 in H3.  eauto. }
      { apply H0. }
Qed.


Lemma setIntuitionR : forall u v, sincl u v \/ u = v -> subset u v.
Proof.
  intros. destruct H as [H1 | h2].
  - inversion H1. apply H.
  - unfold subset. intros. rewrite h2 in H. apply H.
Qed.


Lemma setIntuition : forall u v, sincl u v \/ u = v <-> subset u v.
Proof.
  intros. split.
  - apply setIntuitionR.
  - apply setIntuitionL.
Qed.

(* 将原有的sincl_spec假设去掉，增加了对应的引理并证明。*)
Lemma sincl_spec : forall u v, sincl u v -> sincl v u <-> False.
Proof.
  intros. destruct H as [H1 H2]. destruct H2. destruct H. split.
  - intro H2. destruct H2 as [H2 H3]. unfold subset in H2. generalize (H2 x). intros.
    apply H4 in H. auto.
  - intro. inversion H2.
Qed.


(* 引理名变更，证明对应setDecR做相应更改。*)
Lemma sincl_NotEqual : forall u v, sincl u v -> ~ u = v.
Proof.
  intros. inversion H. inversion H1. destruct H2. apply setDecR. apply H1.
Qed.


Lemma double_inclusion : forall u v, subset u v -> subset v u -> u = v.
Proof.
  intros. apply setIntuition in H. apply setIntuition in H0. destruct H.
  - destruct H0. specialize (sincl_spec u v).
    intros. apply H1 in H. apply H in H0.
    inversion H0. symmetry. apply H0.
  - apply H.
Qed.


(***************************************************************************)
(* 投票行为及性质的定义，并证明一些相关的引理。                                     *)
(***************************************************************************)
(* Formally, a ballot B consisted of the following four components. *)
Record Ballot : Type := mkBallot
{
  (* Bdec A decree (the one being voted on) *)
  dec : decree;
  (* Bqrm A nonempty set of priests (the ballot's quorum) *)
  qrm : set priest;
  (* Bvot A set of priests (the ones who cast votes for the decree) *)
  vot : set priest;
  (* Bbal A ballot number *)
  bal : number;
}.


Hypothesis Aeq_dec_Ballot : forall x y : Ballot, {(bal x) = (bal y)} + {blt_number (bal x) (bal y) = true}.


Variables aBallots : set Ballot.
Variables Acceptors : set priest.
Variables Values : set decree.
Variables Numbers : list number.


Inductive Ballot_Equal_Dec : Ballot -> Ballot -> Prop :=
  | Ballot_Dec_cons : forall b1 b2, set_In b1 aBallots -> set_In b2 aBallots ->
                          b1 = b2 -> (dec b1) = (dec b2)
                                   /\(qrm b1) = (qrm b2)
                                   /\(vot b1) = (vot b2)
                                   /\(bal b1) = (bal b2) -> Ballot_Equal_Dec b1 b2.


Inductive Ballot_bal_Dec : Ballot -> Ballot -> Prop :=
  | Ballot_bal_Dec_cons : forall b1 b2, set_In b1 aBallots -> set_In b2 aBallots ->
    (bal b1) = (bal b2) -> b1 = b2 -> Ballot_bal_Dec b1 b2.


Lemma Ballot_Equal : forall b1 b2, set_In b1 aBallots -> set_In b2 aBallots ->
  Ballot_Equal_Dec b1 b2 -> b1 = b2 -> (dec b1) = (dec b2)
                                   /\(qrm b1) = (qrm b2)
                                   /\(vot b1) = (vot b2)
                                   /\(bal b1) = (bal b2).
Proof.
  intros. inversion H1. apply H6.
Qed.


Lemma Ballot_Equal_decree : forall b1 b2, set_In b1 aBallots -> set_In b2 aBallots ->
  Ballot_Equal_Dec b1 b2 -> b1 = b2 -> (dec b1) = (dec b2).
Proof.
  intros. inversion H1. inversion H6. apply H9.
Qed.


Lemma Ballot_bal : forall b1 b2, set_In b1 aBallots -> set_In b2 aBallots ->
  Ballot_bal_Dec b1 b2 -> (bal b1) = (bal b2) -> b1 = b2.
Proof.
  intros. inversion H1. apply H6.
Qed.


Inductive trivial_qrm : Ballot -> Prop :=
  | trivial_qrm_cons : forall b, set_In b aBallots -> set_In (qrm b) Quorums -> trivial_qrm b.


Inductive trivial_qrm_Acce : Ballot -> priest -> Prop :=
  | trivial_qrm_Acce_cons : forall b a, set_In a (qrm b) -> set_In a Acceptors -> trivial_qrm_Acce b a.


Inductive trivial_decree : Ballot -> Prop :=
  | trivial_decree_cons : forall b, set_In (dec b) Values -> trivial_decree b.


Inductive trivial_number : Ballot -> Prop :=
  | trivial_number_cons : forall b, set_In (bal b) Numbers -> trivial_number b.


Inductive trivial_qrm_vot : Ballot -> Prop :=
  | ttrivial_qrm_vot'_cons : forall b, set_In b aBallots -> subset (vot b) (qrm b) -> trivial_qrm_vot b.


Inductive trivial : Ballot -> Prop :=
  | ttrivial_cons : forall b, trivial_qrm b /\ trivial_decree b /\ trivial_number b /\ trivial_qrm_vot b
                              -> trivial b.


Lemma equalQrmVot : forall b, trivial_qrm_vot b -> subset (qrm b) (vot b) ->  (qrm b) = (vot b).
Proof.
  intros. destruct H. apply double_inclusion.
  apply H0. apply H1.
Qed.


(***************************************************************************)
(* Basic Paxos算法涉及的变量及默认值定义，同时定义了相关性质。                       *)
(***************************************************************************)
Variables maxBal : priest -> number.
Variables maxVBal : priest -> number.
Variables maxVal : priest -> decree.
Variables None : decree.


Definition None_fact : Prop := ~In None Values.


Definition less_or_equal_number (x1 x2 : number) :=
  beq_number x1 x2 = true /\ blt_number x1 x2 = true.


(***************************************************************************)
(* 消息行为抽象，及其性质定义。                                                  *)
(***************************************************************************)
Record MessageNew : Type := mkMessageNew
{
  typeM : nat;         (* 消息的类型。 *)
  balM : number;       (* 消息的轮次。 *)
  maxVBalM : number;   (* 消息的轮次。只有type 2有。 *)
  maxValM : decree;     (* 消息的值。type 2表示曾经参与的最大值，type 3 4表示现阶段进行投票的值，type 1没有。 *)
  accM : priest;       (* 消息的发送者。type 2 4时有，其他的没有。 *)
}.


Variables msgsNew : set MessageNew.


Definition TypeOK : Prop :=
    forall a, In a Acceptors -> In (maxVBal a) Numbers
  /\forall a, In a Acceptors -> In (maxBal a) Numbers
  /\forall a, In a Acceptors -> In (maxVal a) Values
  /\forall a, In a Acceptors -> less_or_equal_number (maxVBal a) (maxBal a).


Inductive VotedForInNew'(m:MessageNew) : priest -> decree -> number -> Prop :=
  | cons_VotedForInNew' : forall a v b, In m msgsNew -> (typeM m) = 4
                                       /\(balM m) = b
                                       /\(maxValM m) = v
                                       /\(accM m) = a -> VotedForInNew' m a v b.


Inductive ChosenInNew'(m:MessageNew)(Q:set priest) : decree -> number -> Prop :=
  | cons_ChosenInNew' : In Q Quorums ->
      forall a v b, set_In a Q -> VotedForInNew' m a v b -> ChosenInNew' m Q v b.


Inductive ChosenNew'(m:MessageNew)(v:decree)(Q:set priest)(b:Ballot)  : decree -> Prop :=
  | cons_ChosenNew' : In b aBallots -> ChosenInNew' m Q v (bal b) -> ChosenNew' m v Q b (dec b).


Hypothesis QrmVotToSucc :
  forall b m, set_In b aBallots -> (qrm b) = (vot b) -> ChosenNew' m (dec b) (qrm b) b (dec b).


Inductive WontVoteInNew'(m:MessageNew) : priest -> number -> Prop := 
  | cons_WontVoteInNew' : forall v a b, In v Values -> ~ VotedForInNew' m a v b
                    /\ blt_number b (maxBal a) = true -> WontVoteInNew' m a b.


Inductive SafeAtNew'(m:MessageNew) : decree -> number -> Prop :=
  | cons_SafeAtNew' : forall c v b, blt_number c b = true ->
    (exists Q,  In Q Quorums ->
      (forall a, In a Q -> VotedForInNew' m a v c \/ WontVoteInNew' m a c)) -> SafeAtNew' m v b.


Inductive MsgInvNew'(m:MessageNew) : Prop :=
  | cons_MsgInvNew' : In m msgsNew -> ((typeM m) = 1 -> True)
                                    /\((typeM m) = 2 -> less_or_equal_number (balM m) (maxBal (accM m))
                                                    /\    (In (maxValM m) Values /\
                                                           In (maxVBalM m) Numbers /\
                                                           VotedForInNew' m (accM m) (maxValM m) (maxVBalM m)
                                                       \/ ((maxValM m) = None /\
                                                           (maxVBalM m) = numberId 0)))
                                    /\((typeM m) = 3 -> (SafeAtNew' m (maxValM m) (balM m)
                                                    /\ forall ma, set_In ma msgsNew -> (typeM m) = 3 ->
                                                        (balM m) = (balM ma) -> (maxValM ma) = (maxValM m)))
                                    /\((typeM m) = 4 -> (less_or_equal_number (balM m) (maxVBal (accM m))
                                                    /\ forall ma, set_In ma msgsNew ->
                                                                  (typeM ma) = 3 /\
                                                                  (balM ma) = (balM m) /\
                                                                  (maxValM ma) = (maxValM m))) -> MsgInvNew' m.



(***************************************************************************)
(* Basic Paxos算法的验证。                                                    *)
(***************************************************************************)
Lemma VotedInv :
  forall m a v b, MsgInvNew' m -> In a Acceptors /\ In v Values /\ In b Numbers /\ set_In m msgsNew ->
                VotedForInNew' m a v b -> less_or_equal_number b (maxVBal a) /\ SafeAtNew' m v b.
Proof.
  intros. inversion H0. inversion H3.
  inversion H5. inversion H1.
  inversion H. inversion H14. inversion H16.
  inversion H18. split.
  - inversion H9. apply H20 in H21.
    inversion H21. inversion H22. 
    inversion H26. rewrite H28 in H23.
    rewrite H25 in H23. apply H23.
  - inversion H9. inversion H22.
    inversion H24. apply H20 in H21.
    inversion H21. specialize (H28 m).
    apply H28 in H7. inversion H7.
    inversion H30. apply H18 in H29.
    inversion H29. rewrite H25 in H33.
    rewrite H23 in H33. apply H33.
Qed.


Lemma VotedInvForSafeAt :
  forall m a v b, MsgInvNew' m -> In a Acceptors /\ In v Values /\ In b Numbers /\ set_In m msgsNew ->
                VotedForInNew' m a v b -> SafeAtNew' m v b.
Proof.
  intros. inversion H0. inversion H3.
  inversion H5. inversion H1.
  inversion H. inversion H14.
  inversion H16. inversion H18.
  inversion H9. inversion H22.
  inversion H24. apply H20 in H21.
  inversion H21. specialize (H28 m).
  apply H28 in H7. inversion H7.
  inversion H30. apply H18 in H29.
  inversion H29. rewrite H25 in H33.
  rewrite H23 in H33. apply H33.
Qed.


Lemma VotedInvForLe :
  forall m a v b, MsgInvNew' m -> In a Acceptors /\ In v Values /\ In b Numbers /\ set_In m msgsNew ->
                VotedForInNew' m a v b -> less_or_equal_number b (maxVBal a).
Proof.
  intros. inversion H0. inversion H3.
  inversion H5. inversion H1.
  inversion H. inversion H14.
  inversion H16. inversion H18.
  inversion H9. apply H20 in H21.
  inversion H21. inversion H22.
  inversion H26. rewrite H28 in H23.
  rewrite H25 in H23. apply H23.
Qed.


Lemma VotedOnce :
  forall a1 a2 b v1 v2 m1 m2, MsgInvNew' m1 -> MsgInvNew' m2 -> In a1 Acceptors ->
  In a2 Acceptors -> In b Numbers -> In v1 Values -> In v2 Values ->
  VotedForInNew' m1 a1 v1 b /\ VotedForInNew' m2 a2 v2 b -> (v1 = v2).
Proof.
  intros. inversion H6.
  inversion H7. inversion H10.
  inversion H15. inversion H17.
  inversion H8. inversion H21.
  inversion H26. inversion H28.
  inversion H. inversion H32.
  inversion H34. inversion H36.
  inversion H0. inversion H40.
  inversion H42. inversion H44.
  apply H38 in H14. inversion H14.
  specialize (H48 m2). apply H48 in H39.
  inversion H39. inversion H50.
  rewrite H29 in H52. rewrite H18 in H52.
  symmetry. apply H52.
Qed.


Lemma SuccToEqual : forall b1 b2, trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2)
  -> (qrm b1) = (vot b1) /\ (qrm b2) = (vot b2).
Proof.
  intros. inversion H.
  inversion H0. split.
  - apply equalQrmVot. inversion H3.
    inversion H8. inversion H10.
    apply H12. apply H1.
  - apply equalQrmVot. inversion H5.
    inversion H8. inversion H10.
    apply H12. apply H2.
Qed.


Lemma SuccToChosen : forall b m, trivial b -> subset (qrm b) (vot b) ->
  ChosenNew' m (dec b) (qrm b) b (dec b).
Proof.
  intros. apply QrmVotToSucc.
  inversion H. inversion H1.
  inversion H4. inversion H6.
  - inversion H3. apply H9.
  - inversion H. inversion H1.
    inversion H3. apply equalQrmVot.
    + inversion H4. inversion H9. apply H11.
    + apply H0.
Qed.


Inductive trivial_vot_msg : MessageNew -> Ballot -> Prop :=
  | trivial_vot_msg_cons : forall b m a, set_In a (vot b) -> (typeM m) = 4
                                                     /\(balM m) = (bal b)
                                                     /\(maxValM m) = (dec b)
                                                     /\(accM m) = a -> trivial_vot_msg m b.


Inductive trivial_vot : MessageNew -> Ballot -> priest -> Prop :=
  | trivial_vot_cons : forall m b a, set_In a (vot b) ->
      VotedForInNew' m a (dec b) (bal b) -> trivial_vot m b a.


Lemma SuccToVoted : forall a b m, trivial b -> subset (qrm b) (vot b) -> trivial_vot m b a ->
  set_In a (qrm b) -> VotedForInNew' m a (dec b) (bal b).
Proof.
  intros. inversion H1. apply H4.
Qed.


Lemma SuccToSafeAt : forall a b m, MsgInvNew' m -> set_In m msgsNew ->
  trivial_qrm_Acce b a -> trivial_vot m b a -> trivial b ->
  subset (qrm b) (vot b) -> SafeAtNew' m (dec b) (bal b).
Proof.
  intros. inversion H1. inversion H2.
  inversion H3. inversion H14.
  inversion H17. inversion H19.
  apply (VotedInvForSafeAt m a).
  - apply H.
  - split.
    + apply H6.
    + inversion H18. split.
      { apply H22. }
      { inversion H20. split.
        - apply H24.
        - apply H0. }
  - apply H10.
Qed.


Hypothesis SafAtInfer : forall b1 b2 m, SafeAtNew' m (dec b2) (bal b2) -> blt_number (bal b1) (bal b2)=true -> (forall a, In a (qrm b2) ->
    VotedForInNew' m a (dec b2) (bal b1) \/ WontVoteInNew' m a (bal b1)).


Lemma SafeAtToVote : forall b1 b2 m a, blt_number (bal b1) (bal b2)=true -> trivial b2 ->
  SafeAtNew' m (dec b2) (bal b2) -> (In a (qrm b2) ->
  VotedForInNew' m a (dec b2) (bal b1) \/ WontVoteInNew' m a (bal b1)).
Proof.
  intros. apply SafAtInfer.
  - apply H1.
  - apply H.
  - apply H2.
Qed.

Hypothesis Vote_Dec : forall m1 m2 b1 b2 a1 a2 v, (In a1 (qrm b1) -> In a2 (qrm b2) -> In v Values ->
    VotedForInNew' m1 a1 (dec b1) (bal b1) -> ~ VotedForInNew' m2 a2 v (bal b1)) -> False.


Theorem FalseToAll : forall b1 b2, False -> (dec b1) = (dec b2).
Proof.
  intros. inversion H.
Qed.


Lemma SafeAtToCons : forall b1 b2 m1 m2 a1 a2, MsgInvNew' m1 -> MsgInvNew' m2 ->
  trivial b1 -> trivial b2 -> trivial_qrm_Acce b1 a1 -> trivial_qrm_Acce b2 a2 ->
  (In a2 (qrm b2) -> VotedForInNew' m2 a2 (dec b2) (bal b1) \/ WontVoteInNew' m2 a2 (bal b1)) ->
  (In a1 (qrm b1) -> VotedForInNew' m1 a1 (dec b1) (bal b1)) -> (dec b1) = (dec b2).
Proof.
  intros. inversion H3.
  apply H6 in H7. inversion H4.
  apply H5 in H11. inversion H11.
  - apply (VotedOnce a1 a2 (bal b1) (dec b1) (dec b2) m1 m2).
    + apply H.
    + apply H0.
    + apply H8.
    + apply H12.
    + inversion H1. inversion H16.
      inversion H19. inversion H21.
      inversion H22. apply H24.
    + inversion H1. inversion H16.
      inversion H19. inversion H20.
      apply H22.
    + inversion H2. inversion H16.
      inversion H19. inversion H20.
      apply H22.
    + split.
      { apply H7. }
      { apply H15. }
  - inversion H15. inversion H17.
    unfold not in H20. apply FalseToAll.
    apply (Vote_Dec m1 m2 b1 b2 a1 a2 v).
    intros. inversion H17. apply H26.
Qed.


Lemma ConsistentOfEqual : forall b1 b2, trivial b1 -> trivial b2 ->
  subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  Ballot_Equal_Dec b1 b2 -> Ballot_bal_Dec b1 b2 ->
  (bal b1) = (bal b2) -> (dec b1) = (dec b2).
Proof.
  intros. apply Ballot_Equal_decree.
  - inversion H. inversion H6.
    inversion H8. apply H10.
  - inversion H0. inversion H6.
    inversion H8. apply H10.
  - apply H3.
  - apply Ballot_bal. inversion H. inversion H6.
    inversion H8. apply H10. inversion H0.
    inversion H6. inversion H8. apply H10.
    apply H4. apply H5.
Qed.


Lemma ConsistentOfNotEqual : forall b1 b2 m1 m2 a1 a2, MsgInvNew' m1 -> MsgInvNew' m2 ->
  trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  In a2 (qrm b2) -> In a1 (qrm b1) -> Ballot_Equal_Dec b1 b2 -> Ballot_bal_Dec b1 b2 ->
  trivial_qrm_Acce b1 a1 -> trivial_qrm_Acce b2 a2 -> trivial_vot m1 b1 a1 -> trivial_vot m2 b2 a2 ->
  blt_number (bal b1) (bal b2)=true -> (dec b1) = (dec b2).
Proof.
  intros. apply (SafeAtToCons b1 b2 m1 m2 a1 a2).
  - apply H.
  - apply H0.
  - apply H1.
  - apply H2.
  - apply H9.
  - apply H10.
  - intros. apply (SafeAtToVote b1 b2 m2 a2).
    + apply H13.
    + apply H2.
    + apply (SuccToSafeAt a2 b2 m2).
      { apply H0. }
      { apply H0. }
      { apply H10. }
      { apply H12. }
      { apply H2. }
      { apply H4. }
    + apply H5.
 - intros. apply (SuccToVoted a1 b1 m1).
    + apply H1.
    + apply H3.
    + apply H11.
    + apply H6.
Qed.


(***************************************************************************)
(* 共识性定理证明。                                                            *)
(***************************************************************************)
Theorem Consistent : forall b1 b2 m1 m2 a1 a2, MsgInvNew' m1 -> MsgInvNew' m2 ->
  trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  In a2 (qrm b2) -> In a1 (qrm b1) -> Ballot_Equal_Dec b1 b2 -> Ballot_bal_Dec b1 b2 ->
  trivial_qrm_Acce b1 a1 -> trivial_qrm_Acce b2 a2 -> trivial_vot m1 b1 a1 -> trivial_vot m2 b2 a2 ->
  (dec b1) = (dec b2).
Proof.
  intros. destruct (Aeq_dec_Ballot b1 b2).
  - apply (ConsistentOfEqual b1 b2).
    + apply H1.
    + apply H2.
    + apply H3.
    + apply H4.
    + apply H7.
    + apply H8.
    + apply e.
  - apply (ConsistentOfNotEqual b1 b2 m1 m2 a1 a2).
    + apply H.
    + apply H0.
    + apply H1.
    + apply H2.
    + apply H3.
    + apply H4.
    + apply H5.
    + apply H6.
    + apply H7.
    + apply H8.
    + apply H9.
    + apply H10.
    + apply H11.
    + apply H12.
    + apply e.
Qed.
