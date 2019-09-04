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


Definition less_or_equal_number (x1 x2 : number) :=
  beq_number x1 x2 = true /\ blt_number x1 x2 = true.


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

(* 论文中的假设条件二。 *)
Hypothesis QuorumsAssumption: forall Q1 Q2, In Q1 Quorums -> In Q2 Quorums ->
  set_inter Aeq_dec Q1 Q2 <> empty_set priest.

(* 论文中的假设条件二。 *)
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


(* 增加Axiom_Set及以下两个推论并证明推论。*)
Axiom Axiom_Set : forall x y : set priest,
  x = y <-> (forall z, In z x <-> In z y).
  

Lemma Axiom_infer1 : forall x y : set priest,
  x <> y <-> ~(forall z, In z x <-> In z y).
Proof.
  intros. apply not_iff_compat. apply Axiom_Set.
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
(* 投票行为及性质的定义，及其性质定义。                                            *)
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


(***************************************************************************)
(* Basic Paxos算法涉及的变量及默认值定义，同时定义了相关性质和引理。                   *)
(***************************************************************************)
Variables aBallots : set Ballot.
Variables Acceptors : set priest.
Variables Values : set decree.
Variables Numbers : list number.


Variables maxBal : priest -> number.
Variables maxVBal : priest -> number.
Variables maxVal : priest -> decree.
Variables None : decree.
Variables msgsNew : set MessageNew.

(* 论文中的假设条件一。 *)
Hypothesis Unique_Ballot : forall x y : Ballot, In x aBallots -> In y aBallots -> x = y <-> (bal x) = (bal y).


Axiom Axiom_Ballot : forall b1 b2,  In b2 aBallots -> In b2 aBallots -> (dec b1) = (dec b2)
                             /\(qrm b1) = (qrm b2)
                             /\(vot b1) = (vot b2)
                             /\(bal b1) = (bal b2) <-> b1 = b2.


Axiom Axiom_MessageNew : forall m1 m2,  In m1 msgsNew -> In m2 msgsNew -> (typeM m1) = (typeM m2)
                             /\(balM m1) = (balM m1)
                             /\(maxValM m1) = (maxValM m2)
                             /\(maxVBalM m1) = (maxVBalM m2)
                             /\(accM m1) = (accM m2) <-> m1 = m2.


Definition None_fact : Prop := ~In None Values.


Definition TypeCheck : Prop :=
    forall a, In a Acceptors -> In (maxVBal a) Numbers
  /\forall a, In a Acceptors -> In (maxBal a) Numbers
  /\forall a, In a Acceptors -> In (maxVal a) Values
  /\forall a, In a Acceptors -> less_or_equal_number (maxVBal a) (maxBal a).


Inductive VotedForInNew : priest -> decree -> number -> Prop :=
  | cons_VotedForInNew : forall a v b, In a Acceptors -> In v Values -> In b Numbers -> (exists m, In m msgsNew /\ (typeM m) = 4
                                       /\(balM m) = b
                                       /\(maxValM m) = v
                                       /\(accM m) = a) -> VotedForInNew a v b.


Inductive ChosenInNew : decree -> number -> Prop :=
  | cons_ChosenInNew : forall v b, In v Values -> In b Numbers -> (exists Q, In Q Quorums ->
      forall a, set_In a Q -> VotedForInNew a v b) -> ChosenInNew v b.


Inductive ChosenNew : decree -> Prop :=
  | cons_ChosenNew : forall v, In v Values -> (exists b, In b Numbers ->
      ChosenInNew v b) -> ChosenNew v.


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


Inductive trivial_decree : Ballot -> Prop :=
  | trivial_decree_cons : forall b, set_In b aBallots -> set_In (dec b) Values -> trivial_decree b.


Inductive trivial_number : Ballot -> Prop :=
  | trivial_number_cons : forall b, set_In b aBallots -> set_In (bal b) Numbers -> trivial_number b.


Inductive trivial_qrm_vot : Ballot -> Prop :=
  | ttrivial_qrm_vot'_cons : forall b, set_In b aBallots -> subset (vot b) (qrm b) -> trivial_qrm_vot b.


Inductive trivial_vot_msg : Ballot -> Prop :=
  | trivial_vot_msg_cons : forall b a, In b aBallots -> set_In a (vot b) -> (exists m, In m msgsNew /\ (typeM m) = 4
                                                     /\(balM m) = (bal b)
                                                     /\(maxValM m) = (dec b)
                                                     /\(accM m) = a) -> trivial_vot_msg b.


Inductive trivial_vot : Ballot -> Prop :=
  | trivial_vot_cons : forall b, In b aBallots -> (forall a, set_In a (vot b) ->
      VotedForInNew a (dec b) (bal b)) -> trivial_vot b.


Inductive trivial_qrm_Acce : Ballot -> Prop :=
  | trivial_qrm_Acce_cons : forall b, set_In b aBallots -> (forall a, set_In a (qrm b) -> set_In a Acceptors) -> trivial_qrm_Acce b.


Inductive trivial : Ballot -> Prop :=
  | ttrivial_cons : forall b, trivial_qrm b /\ trivial_decree b /\ trivial_number b /\ trivial_qrm_vot b
                           /\ trivial_qrm_Acce b /\ trivial_vot b /\ trivial_vot_msg b -> trivial b.


Lemma equalQrmVot : forall b, trivial_qrm_vot b -> subset (qrm b) (vot b) ->  (qrm b) = (vot b).
Proof.
  intros. destruct H. apply double_inclusion.
  apply H0. apply H1.
Qed.


Inductive WontVoteInNew : priest -> number -> Prop :=
  | cons_WontVoteInNew : forall a b, In a Acceptors -> In b Numbers -> (forall v, In v Values -> ~ VotedForInNew a v b)
                    /\ blt_number b (maxBal a) = true -> WontVoteInNew a b.


Inductive SafeAtNew : decree -> number -> Prop :=
  | cons_SafeAtNew : forall v b, In v Values -> In b Numbers ->
      (forall c, In c Numbers -> blt_number c b = true ->
        (
          (exists Q,
              (forall ballot, trivial ballot -> In ballot aBallots -> (c = (bal ballot)) ->
                  Q = (qrm ballot) /\ (forall a, In a Q -> VotedForInNew a v c \/ WontVoteInNew a c)
              )
          )
        )
      )
       -> SafeAtNew v b.


Inductive MsgInvNew : Prop :=
  | cons_MsgInvNew : (forall m, In m msgsNew -> ((typeM m) = 1 -> True)
                                    /\((typeM m) = 2 -> less_or_equal_number (balM m) (maxBal (accM m))
                                                    /\    (In (maxValM m) Values /\
                                                           In (maxVBalM m) Numbers /\
                                                           VotedForInNew (accM m) (maxValM m) (maxVBalM m)
                                                       \/ ((maxValM m) = None /\
                                                           (maxVBalM m) = numberId 0)))
                                    /\((typeM m) = 3 -> (SafeAtNew (maxValM m) (balM m)
                                                    /\ forall ma, set_In ma msgsNew -> (typeM ma) = 3 ->
                                                        (balM ma) = (balM m) -> ma = m))
                                    /\((typeM m) = 4 -> (less_or_equal_number (balM m) (maxVBal (accM m))
                                                    /\ exists ma, set_In ma msgsNew /\
                                                                  (typeM ma) = 3 /\
                                                                  (balM ma) = (balM m) /\
                                                                  (maxValM ma) = (maxValM m)))) -> MsgInvNew.


(***************************************************************************)
(* Basic Paxos算法的验证。                                                    *)
(***************************************************************************)
(* 将原有假设去掉，增加对应的引理并证明。 *)
Lemma QrmVotToSucc :
  forall b a, trivial b -> set_In b aBallots ->
  set_In a (qrm b) -> (qrm b) = (vot b) -> ChosenNew (dec b).
Proof.
  intros. apply cons_ChosenNew.
  - inversion H. inversion H3. inversion H6. inversion H7. apply H10.
  - inversion H. inversion H3. inversion H6. inversion H8. inversion H10.
    inversion H12. inversion H14. inversion H15. generalize (H18 a ); intros. rewrite H2 in H1. apply H20 in H1.
    inversion H1. exists b2. intros. apply (cons_ChosenInNew (dec b) b2).
    + apply H22.
    + apply H28.
    + exists (qrm b). intros. generalize (H18 a1); intros.
      rewrite H2 in H30. apply H31 in H30. rewrite H27. apply H30.
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


Lemma SuccToChosen : forall b a, trivial b -> set_In b aBallots -> set_In a (qrm b) -> subset (qrm b) (vot b) ->
  ChosenNew (dec b).
Proof.
  intros. apply (QrmVotToSucc b a).
  - apply H.
  - apply H0.
  - apply H1.
  - apply equalQrmVot.
    + inversion H. inversion H3.
      inversion H6. inversion H8.
      inversion H10. apply H11.
    + apply H2.
Qed.


Lemma SuccToVoted : forall a b, trivial b -> subset (qrm b) (vot b) ->
  set_In a (qrm b) -> VotedForInNew a (dec b) (bal b).
Proof.
  intros. inversion H. inversion H2.
  inversion H5. inversion H7.
  inversion H9. inversion H11.
  inversion H13. inversion H14.
  generalize (H17 a); intros.
  generalize (equalQrmVot b); intros. 
  apply H20 in H10.
  - rewrite H10 in H1. apply H19 in H1.
    apply H1.
  - apply H0.
Qed.


Lemma VotedInv :
  forall a v b, MsgInvNew -> In a Acceptors /\ In v Values /\ In b Numbers ->
                VotedForInNew a v b -> less_or_equal_number b (maxVBal a) /\ SafeAtNew v b.
Proof.
  intros. inversion H. inversion H1. inversion H6.
  generalize (H2 x); intros. inversion H10. apply H11 in H12.
  inversion H12. inversion H15. inversion H17. inversion H13.
  apply H19 in H20. inversion H20. inversion H21. inversion H25. split.
  - rewrite <- H27. rewrite <- H24. apply H22.
  - inversion H23. inversion H28. generalize (H2 x0); intros. apply H31 in H29.
    inversion H29. inversion H33. inversion H35. inversion H30. apply H36 in H38.
    inversion H38. inversion H39. rewrite <- H26. rewrite <- H24.
    rewrite <- H42. rewrite <- H43. apply H40.
Qed.


Lemma VotedInvForLe :
  forall a v b, MsgInvNew -> In a Acceptors /\ In v Values /\ In b Numbers ->
                VotedForInNew a v b -> less_or_equal_number b (maxVBal a).
Proof.
  intros. inversion H. inversion H1. inversion H6.
  generalize (H2 x); intros. inversion H10. apply H11 in H12.
  inversion H12. inversion H15. inversion H17. inversion H13.
  apply H19 in H20. inversion H20. inversion H21. inversion H25.
  rewrite <- H27. rewrite <- H24. apply H22.
Qed.


Lemma VotedInvForSafeAt :
  forall a v b, MsgInvNew -> In a Acceptors /\ In v Values /\ In b Numbers ->
                VotedForInNew a v b -> SafeAtNew v b.
Proof.
  intros. inversion H. inversion H1. inversion H6.
  generalize (H2 x); intros. inversion H10. apply H11 in H12.
  inversion H12. inversion H15. inversion H17. inversion H13.
  apply H19 in H20. inversion H20. inversion H21. inversion H25.
  inversion H23. inversion H28. generalize (H2 x0); intros. apply H31 in H29.
  inversion H29. inversion H33. inversion H35. inversion H30. apply H36 in H38.
  inversion H38. inversion H39. rewrite <- H26. rewrite <- H24.
  rewrite <- H42. rewrite <- H43. apply H40.
Qed.


Lemma VotedOnce :
  forall a1 a2 b v1 v2, MsgInvNew -> In a1 Acceptors ->
  In a2 Acceptors -> In b Numbers -> In v1 Values -> In v2 Values ->
  VotedForInNew a1 v1 b /\ VotedForInNew a2 v2 b -> (v1 = v2).
Proof.
  intros. inversion H5. inversion H.
  inversion H6. inversion H7.
  inversion H12. inversion H19.
  generalize (H8 x); intros.
  generalize (H8 x0); intros.
  inversion H23. inversion H24.
  apply H25 in H27. apply H26 in H29.
  inversion H27. inversion H32. inversion H34.
  inversion H29. inversion H38. inversion H40.
  inversion H28. inversion H30.
  apply H36 in H43. apply H42 in H45.
  inversion H43. inversion H45.
  inversion H48. inversion H50.
  inversion H51. inversion H52.
  generalize (H8 x1); intros.
  generalize (H8 x2); intros.
  apply H57 in H53. apply H58 in H55.
  inversion H53. inversion H60. inversion H62.
  inversion H55. inversion H66. inversion H68.
  inversion H54. inversion H56.
  apply H63 in H71. apply H69 in H73.
  inversion H71. inversion H73.
  generalize (H76 x2); intros.
  inversion H56. inversion H52. apply H79 in H82.
  - apply Axiom_MessageNew in H82.
    + inversion H54. inversion H56.
      inversion H85. inversion H87.
      inversion H44. inversion H46.
      inversion H93. inversion H95.
      rewrite <- H98. rewrite <- H96.
      rewrite <- H89. rewrite <- H91.
      inversion H82. inversion H101.
      inversion H103. symmetry. apply H104.
    + inversion H52. apply H85.
    + inversion H51. apply H85.
  - inversion H83. apply H84.
  - inversion H81. inversion H72.
    rewrite H86. rewrite H84.
    inversion H44. inversion H46.
    rewrite H88. rewrite H90. auto.
Qed.


Lemma SuccToSafeAt : forall b a, MsgInvNew -> trivial b -> In a (qrm b) ->
  subset (qrm b) (vot b) -> SafeAtNew (dec b) (bal b).
Proof.
  intros. inversion H.
  inversion H0. inversion H4.
  inversion H7. inversion H9.
  inversion H11. inversion H13.
  inversion H15. inversion H14.
  inversion H16. generalize (H19 a); intros.
  generalize (H22 a); intros.
  apply (VotedInvForSafeAt a).
  - apply H.
  - split.
    + apply H24 in H1. apply H1.
    + split.
      { inversion H8. apply H27. }
      { inversion H10. apply H27. }
  - apply SuccToVoted.
    + apply H0.
    + apply H2.
    + apply H1.
Qed.


Lemma SafeAtToVote : forall b1 b2, blt_number (bal b1) (bal b2)=true -> trivial b2 -> trivial b1 ->
  SafeAtNew (dec b2) (bal b2) ->
  (exists a, In a (qrm b1) /\ In a (qrm b2) /\ (VotedForInNew a (dec b2) (bal b1) \/ WontVoteInNew a (bal b1))).
Proof.
  intros. generalize (QuorumsAssumptionE (qrm b1) (qrm b2)); intros.
  inversion H0. inversion H4. inversion H6.
  inversion H1. inversion H11. inversion H13.
  generalize (DoublePredicate (qrm b1) (qrm b2)); intros.
  apply H18 in H16. apply H3 in H16.
  inversion H16. exists x.
  - intros. inversion H2. split.
    + apply set_inter_elim1 in H19. apply H19.
    + split.
      { apply set_inter_elim2 in H19. apply H19. }
      { generalize (H22 (bal b1)); intros.
        inversion H14. inversion H27. inversion H28.
        apply H25 in H31. inversion H31. generalize (H33 b1); intros.
        apply H34 in H1. inversion H1. generalize (H36 x); intros.
        apply set_inter_elim1 in H19. rewrite H35 in H37.
        apply H37 in H19. apply H19.
        - apply H30.
        - auto.
        - apply H. }
  - inversion H4. inversion H19. apply H22.
Qed.


Lemma SafeAtToCons : forall b1 b2 a,
  MsgInvNew -> trivial b1 -> trivial b2 -> In a (qrm b1) -> In a (qrm b2) ->
  (VotedForInNew a (dec b2) (bal b1) \/ WontVoteInNew a (bal b1)) ->
  VotedForInNew a (dec b1) (bal b1) -> (dec b1) = (dec b2).
Proof.
  intros. inversion H4.
  - apply (VotedOnce a a (bal b1) (dec b1) (dec b2)).
    + apply H.
    + inversion H0. inversion H7.
      inversion H10. inversion H12.
      inversion H14. inversion H16.
      inversion H17. generalize (H20 a); intros.
      apply H22 in H2. apply H2.
    + inversion H0. inversion H7.
      inversion H10. inversion H12.
      inversion H14. inversion H16.
      inversion H17. generalize (H20 a); intros.
      apply H22 in H2. apply H2.
    + inversion H0. inversion H7.
      inversion H10. inversion H12.
      inversion H13. apply H16.
    + inversion H0. inversion H7.
      inversion H10. inversion H11.
      apply H14.
    + inversion H1. inversion H7.
      inversion H10. inversion H11.
      apply H14.
    + split.
      { apply H5. }
      { apply H6. }
  - inversion H6. inversion H9.
    generalize (H12 (dec b1)); intros.
    inversion H0. inversion H15.
    inversion H18. inversion H19.
    apply H14 in H22. unfold not in H22.
    apply H22 in H5. inversion H5.
Qed.


Lemma ConsistentOfNotEqual : forall b1 b2, MsgInvNew ->
  trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  blt_number (bal b1) (bal b2)=true -> (dec b1) = (dec b2).
Proof.
  intros. generalize (SafeAtToVote b1 b2); intros.
  apply H5 in H4. inversion H4. apply (SafeAtToCons b1 b2 x).
  - apply H.
  - apply H0.
  - apply H1.
  - inversion H6. apply H7.
  - inversion H6. inversion H8. apply H9.
  - inversion H6. inversion H8. apply H10.
  - generalize (SuccToVoted x b1); intros.
    apply H7 in H0.
    + apply H0.
    + apply H2.
    +inversion H6. apply H8.
  - apply H1.
  - apply H0.
  - inversion H1. inversion H6. inversion H9. inversion H11. inversion H13. inversion H15. inversion H17. inversion H19.
    generalize (SuccToSafeAt b2 a); intros. apply H24 in H.
    + apply H.
    + apply H1.
    + generalize (SuccToEqual b1 b2); intros. apply H25 in H0.
      { inversion H0. rewrite H27. apply H21. }
      { apply H1. }
      { apply H2. }
      { apply H3. }
    + apply H3.
Qed.


Lemma ConsistentOfEqual : forall b1 b2, trivial b1 -> trivial b2 ->
  subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  (bal b1) = (bal b2) -> (dec b1) = (dec b2).
Proof.
  intros. apply (Axiom_Ballot b1 b2).
  - inversion H0. inversion H4. inversion H6. apply H8.
  - inversion H0. inversion H4. inversion H6. apply H8.
  - apply (Unique_Ballot b1 b2).
    + inversion H. inversion H4. inversion H6. apply H8.
    + inversion H0. inversion H4. inversion H6. apply H8.
    + apply H3.
Qed.


(***************************************************************************)
(* 共识性定理证明。                                                            *)
(***************************************************************************)
Theorem Consistent : forall b1 b2, MsgInvNew ->
  trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  (dec b1) = (dec b2).
Proof.
  intros. destruct (Aeq_dec_Ballot b1 b2).
  - apply (ConsistentOfEqual b1 b2).
    + apply H0.
    + apply H1.
    + apply H2.
    + apply H3.
    + apply e.
  - apply (ConsistentOfNotEqual b1 b2).
    + apply H.
    + apply H0.
    + apply H1.
    + apply H2.
    + apply H3.
    + apply e.
Qed.
