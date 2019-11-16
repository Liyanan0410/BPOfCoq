Require Export List.
Require Export ListSet.
Require Export Coq.Init.Nat.
Require Export Coq.Bool.Bool.
Require Export Coq.Logic.Classical.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.


(***************************************************************************)
(* Chapter 0. LIBRARY LEMMAS AND DEFINITIONS                               *)
(***************************************************************************)
(***************************************************************************)
(* Coq库的补充和扩展。                                                        *)
(***************************************************************************)
Definition nat_eq_dec : forall x y: nat, {x = y} + {x <> y}.
  induction x as [|n Hn]; destruct y as [| m].
  - left; reflexivity.
  - right. discriminate.
  - right. discriminate.
  - destruct (Hn m) as [e | d].
    + left; apply f_equal; exact e.
    + right. intro e. apply d. injection e. trivial.
Defined.


(***************************************************************************)
(* Chapter 1. BASIC DEFINITIONS AND PROPERTIES                             *)
(***************************************************************************)
(***************************************************************************)
(* Basic Paxos涉及对象的抽象类型定义，并证明相关定理。                             *)
(***************************************************************************)
Inductive priest : Type :=
  | priestId : nat -> priest.


Inductive decree : Type :=
  | decreeId : nat -> decree.


Inductive number : Type :=
  | numberId : nat -> number.


Definition priest_eq_dec : forall x y:priest, {x = y} + {x <> y}.
  intros [n] [m]. destruct (nat_eq_dec n m) as [e | d].
  - left. apply f_equal. exact e.
  - right. intro e. apply d. injection e; trivial.
Defined.


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
  intros d1. destruct d1 as [n1]. intros d2. destruct d2 as [n2].
  revert n2. induction n1 as [ | n1 IHn1]; intro n2.
  - simpl. destruct n2 as [| n2].
    + intros e. reflexivity.
    + intros e. discriminate e.
  - simpl. destruct n2 as [| n2].
    + intros e. discriminate.
    + intros e. simpl in IHn1. apply IHn1 in e.
      repeat f_equal. injection e. trivial.
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


Definition blt_number (x1 x2 : number) :=
  match x1, x2 with
  | numberId n1, numberId n2 => ltb n1 n2
  end.


Definition less_or_equal_number (x1 x2 : number) :=
  beq_number x1 x2 = true /\ blt_number x1 x2 = true.


Theorem beq_number_true : forall n1 n2 : number,
  beq_number n1 n2 = true -> n1 = n2.
Proof.
  intros n1. destruct n1 as [nat1]. intros n2. destruct n2 as [nat2].
  revert nat2. induction nat1 as [ | nat1 IHn1]; intros nat2.
  - simpl. destruct nat2 as [ | nat2].
    + intros e. reflexivity.
    + intros e. discriminate e.
  - simpl. destruct nat2 as [| nat2].
    + intros e. discriminate.
    + intros e. simpl in IHn1. apply IHn1 in e.
      repeat f_equal. injection e. trivial.
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


(***************************************************************************)
(* Chapter 2. A COMPLEMENT TO THE PROPERTIES OF PRIEST SETS                *)
(***************************************************************************)
(***************************************************************************)
(* 补充priest集合的定义和性质。                                                 *)
(***************************************************************************)
(* 此处的相等是两个priest集合的无序相等性质。 *)
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
  intros x y H. apply not_all_ex_not in H. destruct H as [n H]. unfold iff in H. apply not_and_or in H. destruct H.
  - apply imply_to_and in H. left. exists n. apply H.
  - apply imply_to_and in H. right. exists n. apply H.
Qed.


Definition subset (u v : set priest) := forall a, set_In a u -> set_In a v.


Inductive nincl (u v : set priest) : Prop :=
  nincl_cons : forall a, In a u -> ~ In a v -> nincl u v.


Definition sincl (u v : set priest) := subset u v /\ (exists a, In a v /\ ~In a u).


Lemma setDecR : forall u v : set priest, (exists a, In a v /\ ~In a u) -> u <> v.
Proof.
  intros u v H. destruct H as [a H]. destruct (list_eq_dec priest_eq_dec u v).
  + destruct e. destruct H as [H H1]. eauto.
  + exact n.
Qed.


Lemma setDecL : forall u v : set priest, (exists a, In a u /\ ~In a v) -> u <> v.
Proof.
  intros u v H. destruct H as [a H]. destruct (list_eq_dec priest_eq_dec u v).
  + destruct e. destruct H. eauto.
  + exact n.
Qed.


Lemma set_NotSubset : forall u v : set priest, (exists a, In a v /\ ~In a u) <-> ~ subset v u.
Proof.
  intros; split.
 - intros H1 H2. destruct H1. generalize (H2 x); intro H3. destruct H as [H H1].
   apply H3 in H. auto.
 - intro H. apply not_all_ex_not in H. destruct H. exists x. apply imply_to_and in H. auto.
Qed.


Lemma setIntuitionL : forall u v , subset u v -> sincl u v \/ u = v.
Proof.
  intros u v H. destruct (list_eq_dec priest_eq_dec u v).
  - right. apply e.
  - left. apply Axiom_infer1 in n. apply Axiom_infer2 in n. unfold sincl. split.
    + apply H.
    + unfold subset in H. destruct n as [H1 | H2].
      { destruct H1 as [a H1]. generalize (H a); intros. destruct H1 as [H1 H2]. apply H0 in H1. eauto. }
      { apply H2. }
Qed.


Lemma setIntuitionR : forall u v, sincl u v \/ u = v -> subset u v.
Proof.
  intros u v H. destruct H as [H1 | h2].
  - destruct H1 as [H1 H2]. apply H1.
  - unfold subset. intros a H. rewrite h2 in H. apply H.
Qed.

Lemma setIntuition : forall u v, sincl u v \/ u = v <-> subset u v.
Proof.
  intros. split.
  - apply setIntuitionR.
  - apply setIntuitionL.
Qed.


Lemma sincl_spec : forall u v, sincl u v -> sincl v u <-> False.
Proof.
  intros u v H. destruct H as [H1 H2]. destruct H2 as [a H2]. destruct H2 as [H2 H3]. split.
  - intro H4. destruct H4 as [H4 H5]. unfold subset in H4. generalize (H4 a). intros H.
    apply H in H2. auto.
  - intro. destruct H.
Qed.


Lemma sincl_NotEqual : forall u v, sincl u v -> ~ u = v.
Proof.
  intros u v H. destruct H as [H H1]. apply setDecR. apply H1.
Qed.


Lemma double_inclusion : forall u v, subset u v -> subset v u -> u = v.
Proof.
  intros u v H1 H2. apply setIntuition in H1. apply setIntuition in H2. destruct H1 as [H1 | H3].
  - destruct H2 as [H2 | H4]. specialize (sincl_spec u v).
    intros H. apply H in H1. apply H1 in H2.
    destruct H2. symmetry. apply H4.
  - apply H3.
Qed.


Lemma empty_spec : forall x, ~(set_In x (empty_set priest)).
Proof.
  intros. unfold empty_set. unfold not. simpl. trivial.
Qed.


Lemma empty_spec_iff : forall x, set_In x (empty_set priest) <-> False.
Proof.
  simpl; intros. split; trivial.
Qed.



Lemma empty_spec_mem : forall Q , (exists x, set_mem priest_eq_dec x Q = true) -> Q <> empty_set priest.
Proof.
  intros Q [x e]. apply set_mem_correct1 in e.
  unfold not. intros eQ. rewrite eQ in e. exact e.
Qed.


(***************************************************************************)
(* Chapter 3. BASIC DEFINITIONS AND PROPERTIES OF BALLOT                   *)
(***************************************************************************)
(***************************************************************************)
(* 投票行为的抽象和形式化定义。                                                  *)
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


(***************************************************************************)
(* Chapter 4. BASIC DEFINITIONS AND PROPERTIES OF MESSAGE                  *)
(***************************************************************************)
(***************************************************************************)
(* 消息行为的抽象和形式化定义。                                                  *)
(***************************************************************************)
Record Message : Type := mkMessage
{
  typeM : nat;         (* 消息的类型。 *)
  balM : number;       (* 消息的轮次。 *)
  maxBalM : number;   (* 消息的轮次。只有type 2有。 *)
  maxValM : decree;     (* 消息的值。type 2表示曾经参与的最大值，type 3 4表示现阶段进行投票的值，type 1没有。 *)
  accM : priest;       (* 消息的发送者。type 2 4时有，其他的没有。 *)
}.


(***************************************************************************)
(* Chapter 5. DEFINITIONS OF SYSTEM STATES                                 *)
(***************************************************************************)
(***************************************************************************)
(* 系统状态定义。                                                             *)
(***************************************************************************)
(* 系统所有轮次编号的集合。 *)
Variables Numbers : list number.
(* 系统所有参与者的集合。 *)
Variables Acceptors : set priest.
(* 系统所有待选值的集合，初始为None。 *)
Variables Values : set decree.
Variables None : decree.
(* 系统所有投票的集合。 *)
Variables aBallots : set Ballot.
(* 系统所有轮次参与者集合的集合（议会系统）。 *)
Variables Quorums : set (set priest).
(* 系统所有消息的集合。 *)
Variables msgsChannel : set Message.


(* 每个参与者Promise的最大轮次编号。 *)
Variables PromiseMaxBal : priest -> number.
(* THE WAY TO STATE CONDITION B3。 *)
(* 每个参与者Accepted的最大轮次编号和最大特定值。 *)
Variables AcceptedMaxBal : priest -> number.
Variables AcceptedMaxVal : priest -> decree.


Definition None_fact : Prop := ~In None Values.


(***************************************************************************)
(* Chapter 6. BASIC DEFINITIONS PROPERTIES OF BALLOT AND MESSAGE           *)
(***************************************************************************)
(***************************************************************************)
(* Ballot和Message基本性质的定义和证明。                                        *)
(***************************************************************************)
Lemma characteristic_prop_Ballot : forall b1 b2,  In b1 aBallots -> In b2 aBallots -> (dec b1) = (dec b2)
                             /\(qrm b1) = (qrm b2)
                             /\(vot b1) = (vot b2)
                             /\(bal b1) = (bal b2) <-> b1 = b2.
Proof.
  intros b1 b2 i1 i2. split.
  - destruct b1; destruct b2. simpl. intuition. subst. reflexivity.
  - intro e. subst. auto.
Qed.



Lemma characteristic_prop_Message : forall m1 m2,  In m1 msgsChannel -> In m2 msgsChannel -> (typeM m1) = (typeM m2)
                             /\(balM m1) = (balM m2)
                             /\(maxValM m1) = (maxValM m2)
                             /\(maxBalM m1) = (maxBalM m2)
                             /\(accM m1) = (accM m2) <-> m1 = m2.
Proof.
  intros m1 m2 i1 i2. split.
  - destruct m1; destruct m2. simpl. intuition. subst. reflexivity.
  - intro e. subst. auto.
Qed.


(***************************************************************************)
(* Chapter 7. DEFINITIONS OF PAXOS CONDITIONS AND THESE LEMMAS             *)
(***************************************************************************)
(***************************************************************************)
(* Paxos三大条件以及引理的定义和证明。                                           *)
(***************************************************************************)
(* CONDITION B1 *)
Hypothesis Unique_Ballot : forall x y : Ballot,
  In x aBallots -> In y aBallots -> x = y <-> (bal x) = (bal y).


Hypothesis eq_dec_Ballot : forall x y : Ballot,
  {(bal x) = (bal y)} + {blt_number (bal x) (bal y) = true}.


(* CONDITION B2。 *)
Hypothesis QuorumsAssumption: forall Q1 Q2 : set priest, In Q1 Quorums /\ In Q2 Quorums ->
  exists q, set_In q (set_inter priest_eq_dec Q1 Q2).


Lemma QuorumNonEmptyAuxiliary : forall Q1 Q2, In Q1 Quorums /\ In Q2 Quorums ->
  Q1 <> empty_set priest /\ Q2 <> empty_set priest.
Proof.
  intros Q1 Q2 HQ1Q2. apply QuorumsAssumption in HQ1Q2. destruct HQ1Q2 as [q Hq].
  apply set_inter_elim in Hq. destruct Hq as [Hq1 Hq2]. split.
  - apply empty_spec_mem. exists q.
    apply set_mem_correct2. apply Hq1.
  - apply empty_spec_mem. exists q.
    apply set_mem_correct2. apply Hq2.
Qed.


Lemma QuorumNonEmpty : forall Q, In Q Quorums -> Q <> empty_set priest.
Proof.
  intros Q H. specialize (QuorumNonEmptyAuxiliary Q Q); intros HQ.
  assert (HD : forall Q, In Q Quorums -> In Q Quorums /\ In Q Quorums ).
    { intros AQ AH. split.
      + exact AH.
      + exact AH. }
  specialize (HD Q); intros.
  apply HD in H. apply HQ in H.
  destruct H as [H1 H2]. apply H1.
Qed.


(***************************************************************************)
(* Chapter 8. DEFINITIONS ABOUT HOW A VALUE IS CHOSEN                      *)
(***************************************************************************)
(***************************************************************************)
(* 特定值被选择的定义，即公式（2）。                                              *)
(***************************************************************************)
Inductive VotedForIn : priest -> decree -> number -> Prop :=
  | cons_VotedForIn : forall a v b, In a Acceptors -> In v Values -> In b Numbers ->
    (exists m, In m msgsChannel /\ (typeM m) = 4
                                /\ (balM m) = b
                                /\ (maxValM m) = v
                                /\ (accM m) = a) -> VotedForIn a v b.


Inductive SuccessfulIn : decree -> number -> Prop :=
  | cons_SuccessfulIn : forall v b, In v Values -> In b Numbers -> (exists Q, In Q Quorums ->
      forall a, set_In a Q -> VotedForIn a v b) -> SuccessfulIn v b.


Inductive Chosen : decree -> Prop :=
  | cons_Chosen : forall v, In v Values -> (exists b, In b Numbers ->
      SuccessfulIn v b) -> Chosen v.


(***************************************************************************)
(* Chapter 9. DEFINITIONS OF BALLOT RELIABILITY AND NONTAMPERABILITY       *)
(***************************************************************************)
(***************************************************************************)
(* 每个投票轮次的真实性和不可篡改性的定义。                                         *)
(***************************************************************************)
Inductive trivial_qrm : Ballot -> Prop :=
  | trivial_qrm_cons : forall b, set_In b aBallots -> set_In (qrm b) Quorums -> trivial_qrm b.


Inductive trivial_decree : Ballot -> Prop :=
  | trivial_decree_cons : forall b, set_In b aBallots -> set_In (dec b) Values -> trivial_decree b.


Inductive trivial_number : Ballot -> Prop :=
  | trivial_number_cons : forall b, set_In b aBallots -> set_In (bal b) Numbers -> trivial_number b.


Inductive trivial_qrm_vot : Ballot -> Prop :=
  | ttrivial_qrm_vot_cons : forall b, set_In b aBallots -> subset (vot b) (qrm b) -> trivial_qrm_vot b.


Inductive trivial_vot_msg : Ballot -> Prop :=
  | trivial_vot_msg_cons : forall b a, In b aBallots -> set_In a (vot b) ->
      (exists m, In m msgsChannel -> (typeM m) = 4
                                  /\ (balM m) = (bal b)
                                  /\ (maxValM m) = (dec b)
                                  /\ (accM m) = a) -> trivial_vot_msg b.


Inductive trivial_vot : Ballot -> Prop :=
  | trivial_vot_cons : forall b, In b aBallots -> (forall a, set_In a (vot b) ->
      VotedForIn a (dec b) (bal b)) -> trivial_vot b.


Inductive trivial_qrm_Acce : Ballot -> Prop :=
  | trivial_qrm_Acce_cons : forall b, set_In b aBallots ->
      (forall a, set_In a (qrm b) -> set_In a Acceptors) -> trivial_qrm_Acce b.


Inductive trivial (b : Ballot) : Prop :=
  | ttrivial_cons : trivial_qrm b -> trivial_decree b -> trivial_number b -> trivial_qrm_vot b
      -> trivial_qrm_Acce b -> trivial_vot b -> trivial_vot_msg b -> trivial b.




(***************************************************************************)
(* Chapter 10. DEFINITIONS AND PROPERTIES OF SYSTEM VOTES STATE            *)
(***************************************************************************)
(***************************************************************************)
(* 系统投票状态的定义。                                                        *)
(***************************************************************************)
(* 参与者没有在某一轮次投票，并且以后也不会在这一轮次投票。 *)
Inductive WontVoteIn : priest -> number -> Prop :=
  | cons_WontVoteIn : forall a b, In a Acceptors -> In b Numbers ->
         (forall v, In v Values -> ~ VotedForIn a v b)
      /\ blt_number b (PromiseMaxBal a) = true -> WontVoteIn a b.

(* 在任何轮次编号小与b的投票轮次中，除了v以外，没有别的特定值被选择，或者永远不会被选择，称为在（b, v）投票轮次稳定。 *)
Inductive SafeAt : decree -> number -> Prop :=
  | cons_SafeAt : forall v b, In v Values -> In b Numbers ->
      (forall c, In c Numbers -> blt_number c b = true ->
        (
          (exists Q,
              (forall ballot, trivial ballot -> In ballot aBallots -> (c = (bal ballot)) ->
                  Q = (qrm ballot) /\ (forall a, In a Q -> VotedForIn a v c \/ WontVoteIn a c)
              )
          )
        )
      )
       -> SafeAt v b.


(***************************************************************************)
(* Chapter 11. DEFINITIONS OF PAXOS ALL PHASES                             *)
(***************************************************************************)
(***************************************************************************)
(* Paxos四个阶段的定义，分别对应系统中产生四条消息。                                *)
(***************************************************************************)
Inductive MsgInv : Prop :=
  | cons_MsgInv : (forall m, In m msgsChannel ->
        ((typeM m) = 1 -> True)
     /\ ((typeM m) = 2 -> less_or_equal_number (balM m) (PromiseMaxBal(accM m))
                      /\    (In (maxValM m) Values /\
                             In (maxBalM m) Numbers /\
                             VotedForIn (accM m) (maxValM m) (maxBalM m)
                         \/ ((maxValM m) = None /\
                             (maxBalM m) = numberId 0)))
     /\((typeM m) = 3 -> (SafeAt (maxValM m) (balM m)
                      /\ forall ma, set_In ma msgsChannel -> (typeM ma) = 3 ->
                            (balM ma) = (balM m) -> ma = m))
     /\((typeM m) = 4 -> (less_or_equal_number (balM m) (AcceptedMaxBal (accM m))
                      /\ exists ma, set_In ma msgsChannel
                                 /\ (typeM ma) = 3
                                 /\ (balM ma) = (balM m)
                                 /\ (maxValM ma) = (maxValM m)))) -> MsgInv.


(***************************************************************************)
(* Chapter 12. VERIFICATION OF BASIC PAXOS                                 *)
(***************************************************************************)
(***************************************************************************)
(* Basic Paxos算法的验证。                                                    *)
(***************************************************************************)
Lemma equalQrmVot : forall b, trivial_qrm_vot b -> subset (qrm b) (vot b) -> (qrm b) = (vot b).
Proof.
  intros b H1 H2. destruct H1 as [b H1 H3]. apply double_inclusion.
  - exact H2.
  - exact H3.
Qed.


Lemma QrmVotToSucc :
  forall b a, trivial b -> set_In b aBallots ->
  set_In a (qrm b) -> (qrm b) = (vot b) -> Chosen (dec b).
Proof.
  intros b a H H0 H1 H2.
  destruct H as [H3 H4 H5 H6 H7 H8 H9]. apply cons_Chosen.
  - destruct H4 as [b H H4]. exact H4.
  - destruct H8 as [b H8 H10]. generalize (H10 a ); intros H11.
    rewrite H2 in H1. apply H11 in H1.
    destruct H1 as [ a v b0 H H1 H12 H13]. exists b0. intros H15.
    apply (cons_SuccessfulIn v b0).
    + exact H1.
    + exact H15.
    + exists (qrm b). intros. generalize (H10 a0); intros.
      rewrite H2 in H16. apply H17 in H16. apply H16.
Qed.


Lemma SuccToEqual : forall b1 b2, trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2)
  -> (qrm b1) = (vot b1) /\ (qrm b2) = (vot b2).
Proof.
  intros b1 b2 H H0 H1 H2. destruct H as [H H3 H4 H5 H6 H7 H8].
  destruct H0 as [H0 H9 H10 H11 H12 H13 H14]. split.
  - apply equalQrmVot.
    + apply H5.
    + apply H1.
  - apply equalQrmVot.
    + apply H11.
    + exact H2.
Qed.


Lemma SuccToChosen : forall b a, trivial b -> set_In b aBallots -> set_In a (qrm b) -> subset (qrm b) (vot b) ->
  Chosen (dec b).
Proof.
  intros b a H H0 H1 H2. apply (QrmVotToSucc b a).
  - apply H.
  - apply H0.
  - apply H1.
  - apply equalQrmVot.
    + destruct H as [H H3 H4 H5 H6 H7 H8]. apply H5.
    + apply H2.
Qed.


Lemma SuccToVoted : forall a b, trivial b -> subset (qrm b) (vot b) ->
  set_In a (qrm b) -> VotedForIn a (dec b) (bal b).
Proof.
  intros a b H H0 H1. destruct H as [H H2 H3 H4 H5 H6 H7].
  destruct H6 as [b H6 H8].
  generalize (H8 a); intros H9.
  generalize (equalQrmVot b); intros H10.
  apply H10 in H4.
  - rewrite H4 in H1. apply H9 in H1.
    apply H1.
  - exact H0.
Qed.


Lemma VotedInv :
  forall a v b, MsgInv -> In a Acceptors /\ In v Values /\ In b Numbers ->
                VotedForIn a v b -> less_or_equal_number b (AcceptedMaxBal a) /\ SafeAt v b.
Proof.
  intros a v b H H0 H1. destruct H. destruct H1 as [a v b H1 H2 H3 H4].
  destruct H4 as [x H4]. generalize (H x); intros H5.
  destruct H4 as [H4 H6]. apply H5 in H4. destruct H4 as [H4 H7].
  destruct H7 as [H7 H8]. destruct H8 as [H8 H9]. destruct H6 as [H6 H10].
  apply H9 in H6. destruct H6 as [H6 H11]. destruct H10 as [H10 H12].
  destruct H12 as [H12 H13]. split.
  - rewrite <- H10. rewrite <- H13. apply H6.
  - destruct H11 as [ma H11]. generalize (H ma); intros H14.
    destruct H11 as [H11 H15]. apply H14 in H11. destruct H11 as [H11 H16].
    destruct H16 as [H16 H17]. destruct H17 as [H17 H18].
    destruct H15 as [H15 H19]. apply H17 in H15. destruct H15 as [H15 H20].
    destruct H19 as [H19 H21]. rewrite <- H12. rewrite <- H10.
    rewrite <- H19. rewrite <- H21. apply H15.
Qed.


Lemma VotedInvForLe :
  forall a v b, MsgInv -> In a Acceptors /\ In v Values /\ In b Numbers ->
                VotedForIn a v b -> less_or_equal_number b (AcceptedMaxBal a).
Proof.
  intros a v b H H0 H1. destruct H. destruct H1 as [a v b H1 H2 H3 H4].
  destruct H4 as [m H4]. specialize (H m); intros.
  destruct H4 as [H4 H5]. apply H in H4.
  destruct H4 as [H4 H6]. destruct H6 as [H6 H7].
  destruct H7 as [H7 H8]. destruct H5 as [H5 H9].
  apply H8 in H5. destruct H9 as [H9 H10].
  destruct H10 as [H10 H11]. destruct H5 as [H5 H12].
  rewrite <- H9. rewrite <- H11. apply H5.
Qed.


Lemma VotedInvForSafeAt :
  forall a v b, MsgInv -> In a Acceptors /\ In v Values /\ In b Numbers ->
                VotedForIn a v b -> SafeAt v b.
Proof.
  intros a v b H H0 H1. destruct H. destruct H1 as [a v b H1 H2 H3 H4].
  destruct H4 as [m H4]. generalize (H m); intros H5.
  destruct H4 as [H4 H6]. apply H5 in H4.
  destruct H4 as [H4 H7]. destruct H7 as [H7 H8].
  destruct H8 as [H8 H9]. destruct H6 as [H6 H10].
  apply H9 in H6. destruct H6 as [H6 H11].
  destruct H10 as [H10 H12]. destruct H12 as [H12 H13].
  destruct H11 as [ma H11]. destruct H11 as [H11 H14].
  specialize (H ma); intros. apply H in H11.
  destruct H11 as [H11 H15]. destruct H15 as [H15 H16].
  destruct H16 as [H16 H17]. destruct H14 as [H14 H18].
  apply H16 in H14. destruct H14 as [H14 H19].
  rewrite <- H12. rewrite <- H10.
  destruct H18 as [H18 H20].
  rewrite <- H18. rewrite <- H20. exact H14.
Qed.


Lemma VotedOnce :
  forall a1 a2 b v1 v2, MsgInv -> In a1 Acceptors ->
  In a2 Acceptors -> In b Numbers -> In v1 Values -> In v2 Values ->
  VotedForIn a1 v1 b /\ VotedForIn a2 v2 b -> (v1 = v2).
Proof.
  intros a1 a2 b v1 v2 H H0 H1 H2 H3 H4 H5.
  destruct H5 as [H5 H6]. destruct H.
  destruct H5 as [a1 v1 b H5 H7 H8 H9].
  destruct H6 as [a2 v2 b H6 H10 H11 H12].
  destruct H9 as [m1 H9].
  destruct H12 as [m2 H12].
  generalize (H m1); intros H13.
  generalize (H m2); intros H14.
  destruct H9 as [H9 H15]. destruct H15 as [H15 H16].
  destruct H16 as [H16 H17]. destruct H17 as [H17 H18].
  destruct H12 as [H12 H19]. destruct H19 as [H19 H20].
  destruct H20 as [H20 H21]. destruct H21 as [H21 H22].
  apply H13 in H9. apply H14 in H12.
  destruct H9 as [H9 H23]. destruct H23 as [H23 H24].
  destruct H24 as [H24 H25]. destruct H12 as [H12 H26].
  destruct H26 as [H26 H27]. destruct H27 as [H27 H28].
  apply H25 in H15. apply H28 in H19.
  destruct H15 as [H15 H29]. destruct H19 as [H19 H30].
  destruct H29 as [m3 H29]. destruct H30 as [m4 H30].
  destruct H29 as [H29 H31]. destruct H31 as [H31 H32].
  destruct H32 as [H32 H33]. destruct H30 as [H30 H34].
  destruct H34 as [H34 H35]. destruct H35 as [H35 H36].
  generalize (H m3); intros H37.
  generalize (H m4); intros H38.
  assert ( H29Copy := H29 ). apply H37 in H29.
  assert ( H30Copy := H30 ). apply H38 in H30.
  destruct H29 as [H29 H39]. destruct H39 as [H39 H40].
  destruct H40 as [H40 H41]. destruct H30 as [H30 H42].
  destruct H42 as [H42 H43]. destruct H43 as [H43 H44].
  assert ( H31Copy := H31 ).
  assert ( H34Copy := H34 ).
  apply H40 in H31. apply H43 in H34.
  destruct H31 as [H31 H45]. destruct H34 as [H34 H46].
  generalize (H45 m4); intros H47.
  assert ( H30CopyTwo := H30Copy ). apply H47 in H30Copy.
  - apply characteristic_prop_Message in H30Copy.
    + destruct H30Copy as [H48 H49].
      destruct H49 as [H49 H50].
      destruct H50 as [H50 H51].
      destruct H51 as [H51 H52].
      rewrite <- H21. rewrite <- H17.
      rewrite <- H36. rewrite <- H33.
      symmetry. exact H50.
    + exact H30CopyTwo.
    + exact H29Copy.
  - exact H34Copy.
  - rewrite H35. rewrite H32.
    rewrite H16. rewrite H20.
    auto.
Qed.


Lemma SuccToSafeAt : forall b a, MsgInv -> trivial b -> In a (qrm b) ->
  subset (qrm b) (vot b) -> SafeAt (dec b) (bal b).
Proof.
  intros b a H H0 H1 H2. assert ( HCopy := H ).
  destruct H. assert ( H0Copy := H0 ).
  destruct H0 as [H3 H4 H5 H6 H7 H8 H9].
  destruct H7 as [b H7 H10].
  specialize (H10 a); intros.
  apply (VotedInvForSafeAt a).
  - apply HCopy.
  - split.
    + apply H10 in H1. exact H1.
    + split.
      { destruct H4 as [b H4 H11]. exact H11. }
      { destruct H5 as [b H5 H12]. exact H12. }
  - apply SuccToVoted.
    + apply H0Copy.
    + apply H2.
    + apply H1.
Qed.


Lemma SafeAtToVote : forall b1 b2, blt_number (bal b1) (bal b2)=true -> trivial b2 -> trivial b1 ->
  SafeAt (dec b2) (bal b2) ->
  (exists a, In a (qrm b1) /\ In a (qrm b2) /\ (VotedForIn a (dec b2) (bal b1) \/ WontVoteIn a (bal b1))).
Proof.
  intros b1 b2 H H0 H1 H2.
  generalize (QuorumsAssumption (qrm b1) (qrm b2)); intros H3.
  assert ( H0Copy := H0 ). assert ( H1Copy := H1 ).
  destruct H0 as [H4 H5 H6 H7 H8 H9 H10].
  destruct H1 as [H11 H12 H13 H14 H15 H16 H17].
  assert (HD : forall Q1 Q2, In Q1 Quorums -> In Q2 Quorums -> In Q1 Quorums /\ In Q2 Quorums ).
    { intros Q1 Q2 HQ1 HQ2. split.
      + exact HQ1.
      + exact HQ2. }
  specialize (HD (qrm b1) (qrm b2)); intros.
  destruct H4 as [b2 H4 H19].
  destruct H11 as [b1 H11 H20].
  apply HD in H20. apply H3 in H20.
  destruct H20 as [q H20].
  - exists q. destruct H2 as [v n H2 H21 H22]. split.
    + apply set_inter_elim1 in H20. exact H20.
    + split.
      { apply set_inter_elim2 in H20. exact H20. }
      { specialize (H22 (bal b1)); intros.
        destruct H13 as [b1 H13 H23].
        apply H22 in H23. destruct H23 as [Q H23].
        specialize (H23 b1); intros.
        apply H23 in H1Copy. destruct H1Copy as [H1Copy H24].
        specialize (H24 q); intros. apply set_inter_elim1 in H20.
        rewrite H1Copy in H24. apply H24 in H20.
        - exact H20.
        - exact H13.
        - auto.
        - exact H. }
  - apply H19.
Qed.


Lemma SafeAtToCons : forall b1 b2 a,
  MsgInv -> trivial b1 -> trivial b2 -> In a (qrm b1) -> In a (qrm b2) ->
  (VotedForIn a (dec b2) (bal b1) \/ WontVoteIn a (bal b1)) ->
  VotedForIn a (dec b1) (bal b1) -> (dec b1) = (dec b2).
Proof.
  intros b1 b2 a H H0 H1 H2 H3 H4 H5.
  destruct H0 as [H6 H7 H8 H9 H10 H11 H12].
  destruct H1 as [H13 H14 H15 H16 H17 H18 H19].
  destruct H4 as [H4Left | H4Right].
  - apply (VotedOnce a a (bal b1) (dec b1) (dec b2)).
    + exact H.
    + destruct H10 as [b1 H10 H20].
      specialize (H20 a); intros.
      apply H20 in H2. exact H2.
    + destruct H10 as [b1 H10 H20].
      specialize (H20 a); intros.
      apply H20 in H2. exact H2.
    + destruct H8 as [b1 H8 H20].
      exact H20.
    + destruct H7 as [b1 H7 H20].
      exact H20.
    + destruct H14 as [b2 H14 H20].
      exact H20.
    + split.
      { apply H5. }
      { apply H4Left. }
  - destruct H4Right as [a n H4Right1 H4Right2 H4Right3].
    destruct H4Right3 as [H4Right3 H4Right4].
    specialize (H4Right3 (dec b1)); intros.
    destruct H7 as [b1 H7 H20].
    apply H4Right3 in H20. unfold not in H20.
    apply H20 in H5. destruct H5.
Qed.


Lemma ConsistentOfNotEqual : forall b1 b2, MsgInv ->
  trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  blt_number (bal b1) (bal b2)=true -> (dec b1) = (dec b2).
Proof.
  intros b1 b2 H H0 H1 H2 H3 H4.
  generalize (SafeAtToVote b1 b2); intros H5.
  apply H5 in H4. destruct H4 as [x H4].
  destruct H4 as [H4 H6]. destruct H6 as [H6 H7].
  apply (SafeAtToCons b1 b2 x).
  - apply H.
  - apply H0.
  - apply H1.
  - exact H4.
  - exact H6.
  - exact H7.
  - generalize (SuccToVoted x b1); intros H8.
    apply H8 in H0.
    + apply H0.
    + apply H2.
    + apply H4.
  - apply H1.
  - apply H0.
  - assert ( H1Copy := H1 ). destruct H1 as [H1 H6 H7 H8 H9 H10 H11].
    destruct H11 as [b2 a H11 H12 H13].
    generalize (SuccToSafeAt b2 a); intros H14.
    apply H14 in H.
    + exact H.
    + exact H1Copy.
    + generalize (SuccToEqual b1 b2); intros H15.
      apply H15 in H0.
      { destruct H0 as [H0 H16].
        rewrite H16. exact H12. }
      { exact H1Copy. }
      { exact H2. }
      { exact H3. }
    + exact H3.
Qed.


Lemma ConsistentOfEqual : forall b1 b2, trivial b1 -> trivial b2 ->
  subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  (bal b1) = (bal b2) -> (dec b1) = (dec b2).
Proof.
  intros b1 b2 H H0 H1 H2 H3.
  apply (characteristic_prop_Ballot b1 b2).
  - destruct H as[H11 H12 H13 H14 H15 H16 H17].
    destruct H11 as [b1 H11 H18]. exact H11.
  - destruct H0 as[H4 H5 H6 H7 H8 H9 H10].
    destruct H4 as [b2 H4 H19]. exact H4.
  - apply (Unique_Ballot b1 b2).
    + destruct H as[H11 H12 H13 H14 H15 H16 H17].
      destruct H11 as [b1 H11 H18]. exact H11.
    + destruct H0 as[H4 H5 H6 H7 H8 H9 H10].
      destruct H4 as [b2 H4 H19]. exact H4.
    + exact H3.
Qed.


(***************************************************************************)
(* 共识性定理证明。                                                            *)
(***************************************************************************)
(***************************************************************************)
(* Consistent                                                           *)
(***************************************************************************)
Theorem Consistent : forall b1 b2, MsgInv ->
  trivial b1 -> trivial b2 -> subset (qrm b1) (vot b1) -> subset (qrm b2) (vot b2) ->
  (dec b1) = (dec b2).
Proof.
  intros b1 b2 H H0 H1 H2 H3.
  destruct (eq_dec_Ballot b1 b2).
  - apply (ConsistentOfEqual b1 b2).
    + apply H0.
    + apply H1.
    + apply H2.
    + apply H3.
    + apply e.
  - apply (ConsistentOfNotEqual b1 b2).
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact e.
Qed.


(***************************************************************************)
(* Chapter 13. A CONCRETE EXAMPLE                                          *)
(***************************************************************************)
(***************************************************************************)
(* Lamport论文中的具体例子。                                                   *)
(***************************************************************************)
(*具体例子对单个投票的抽象。*)
Record Vote : Type := mkVote
{
  (* A priest *)
  Vpriest : priest;
  (* A ballot number *)
  Vbal : number;
  (* A decree *)
  Vdec : decree;
}.


(* 系统中共有五个参与者，组成acceptors。涉及到两个特定值以及五个轮次的投票行为。*)
Definition accPA := priestId 1.
Definition accPB := priestId 2.
Definition accPC := priestId 3.
Definition accPD := priestId 4.
Definition accPE := priestId 5.


Definition acceptors := [accPA; accPB; accPC; accPD; accPE].


Definition valueA := decreeId 1.
Definition valueB := decreeId 2.


Definition number2 := numberId 2.
Definition number5 := numberId 5.
Definition number14 := numberId 14.
Definition number27 := numberId 27.
Definition number29 := numberId 29.


Definition ballot_2 := mkBallot valueA [accPA; accPB; accPC; accPD] [accPD] number2.
Definition ballot_5 := mkBallot valueB [accPA; accPB; accPC; accPE] [accPC] number5.
Definition ballot_14 := mkBallot valueA [accPB; accPD; accPE] [accPB; accPE] number14.
Definition ballot_27 := mkBallot valueB [accPA; accPC; accPD] [accPA; accPC; accPD] number27.
Definition ballot_29 := mkBallot valueB [accPB; accPC; accPD] [accPB] number29.


Definition Ballots := [ballot_2; ballot_5; ballot_14; ballot_27; ballot_29].


(* 以下过程用来说明：在ballot_27轮次之后，系统选择的所有特定值都满足一致性。*)
(* get一轮投票的所有投票。 *)
Fixpoint getPriestsVotes(l : list priest)(b : Ballot) : list Vote :=
  match l with
  | [] => []
  | h :: r => mkVote h (bal b) (dec b) :: getPriestsVotes r b
  end.


Definition getBallotVotes(b : Ballot) : list Vote := getPriestsVotes (vot b) b.


(* get所有轮投票的所有投票。 *)
Fixpoint getAllVotes(l : list Ballot) : list Vote :=
  match l with
  | [] => []
  | x :: r => getBallotVotes x ++ getAllVotes r
  end.


Definition votes := getAllVotes aBallots.


(* get特定参与者一轮投票的所有投票。 *)
Fixpoint isIn (x:priest)(l:list priest) : bool :=
  match l with
  | [] => false
  | h::t => if beq_priest x h then true
            else isIn x t
  end.


Fixpoint getBallotVoteForPriest(p : priest)(b : Ballot) : Vote :=
  if isIn p (vot b) then mkVote p (bal b) (dec b)
  else mkVote p (numberId 0) None.

(* get特定参与者所有轮投票的所有投票。 *)
Fixpoint getAllVotesForPriest(p : priest)(l : list Ballot) : list Vote :=
  match l with
  | [] => []
  | h :: r => getBallotVoteForPriest p h :: getAllVotesForPriest p r
  end.


Fixpoint maxVotes (e: Vote) (l : list Vote) : Vote :=
  match l with
  | [] => e
  | x :: r => if blt_number (Vbal e) (Vbal x) then maxVotes x r else maxVotes e r
  end.


(* get每个参与者在所有轮投票中的最大投票列表。 *)
Fixpoint maxs(lp : list priest)(lv : list Ballot) : list Vote :=
  match lp with
  | [] => []
  | h :: r => maxVotes (mkVote h (numberId 0) None) (getAllVotesForPriest h lv) :: maxs r lv
  end.


(* get所有参与者在所有轮投票中的最大投票。 *)
Fixpoint MaxOfAll(e: Vote)(l : list Vote) : Vote :=
  match l with
  | [] => e
  | h :: r => if blt_number (Vbal e) (Vbal h) then MaxOfAll h r else MaxOfAll e r
  end.

(* 对以上定义的检测：通过执行可以确保定义的正确性。 *)
Compute MaxOfAll (mkVote accPA (numberId 0) None) (maxs [accPA; accPB; accPC; accPD; accPE] Ballots).
Compute maxs [accPA; accPB; accPC; accPD; accPE] Ballots.


Theorem max_A : maxVotes (mkVote accPA (numberId 0) None) (getAllVotesForPriest accPA Ballots)
    = (mkVote accPA (numberId 27) valueB).
Proof.
  simpl. reflexivity.
Qed.


Theorem max_B : maxVotes (mkVote accPB (numberId 0) None) (getAllVotesForPriest accPB Ballots)
    = (mkVote accPB (numberId 29) valueB).
Proof.
  simpl. reflexivity.
Qed.


Theorem max_C : maxVotes (mkVote accPC (numberId 0) None) (getAllVotesForPriest accPC Ballots)
    = (mkVote accPC (numberId 27) valueB).
Proof.
  simpl. reflexivity.
Qed.


Theorem max_D : maxVotes (mkVote accPD (numberId 0) None) (getAllVotesForPriest accPD Ballots)
    = (mkVote accPD (numberId 27) valueB).
Proof.
  simpl. reflexivity.
Qed.


Theorem max_E : maxVotes (mkVote accPE (numberId 0) None) (getAllVotesForPriest accPE Ballots)
    = (mkVote accPE (numberId 14) valueA).
Proof.
  simpl. reflexivity.
Qed.


Theorem max_OfAll : MaxOfAll (mkVote accPA (numberId 0) None) (maxs [accPA; accPB; accPC; accPD; accPE] Ballots)
    = (mkVote accPB (numberId 29) valueB).
Proof.
  simpl. reflexivity.
Qed.


(* 在Paxos假设满足的情况下，ballot_27轮次之后系统所选的特定值都保持一致。*)
Hypothesis conditionOfMax : forall b : Ballot, (dec b)
  = Vdec (MaxOfAll (mkVote accPA (numberId 0) None) (maxs [accPA; accPB; accPC; accPD; accPE] Ballots)).


Theorem ExampleOfConsistent : forall b : Ballot, blt_number (bal ballot_27) (bal b) = true ->
  (dec b) = dec ballot_27.
Proof.
  intros. apply (conditionOfMax b).
Qed.
