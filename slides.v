  Definition Even (n : nat) := exists k, n = 2 * k.
  Definition Odd  (m : nat) := exists l, m = 2 * l + 1.
  
  Lemma EvenToOdd : forall (n : nat), Even n -> Odd (n + 1).
  Proof.
    intros.
    unfold Even in H.
    destruct H as [k].
    unfold Odd.
    exists k.
    rewrite <- H.
    reflexivity.
  Qed.

  Require Import String.
  Require Import trivial.DataTypeOps.
  Require Import trivial.LayerCONTRACT.

  Require Import DeepSpec.lib.Monad.StateMonadOption.
  Require Import DeepSpec.lib.Monad.RunStateTInv.
  Require Import lib.ArithInv.
  Import DeepSpec.lib.Monad.Monad.MonadNotation.

  Require Import Lia.
  Require Import List.
  Require Import Bool.
  Require Import ZArith.
  Require Import cclib.Maps.
  Require Import cclib.Integers.

  Require Import DataTypes.
  Require Import backend.MachineModel.

  Require Import DataTypes.
  Import ListNotations.

  Require Import core.MemoryModel. 
  Require Import HyperTypeInst.

  Require Import Maps.
  Import Maps.Int256Tree_Properties.
  Import Maps.Int256Tree.

  Require Import trivial.ContractModel.
  Import trivial.ContractModel.ContractModel.

  Require Import Syntax.
  
  Open Scope Z.

  Section Proof.  
  Context (contract_address : addr).
  Context {memModelOps : MemoryModelOps mem}.


  Require Import Syntax. (* .none *)
  Print Trivial_boolToInt_opt.
  Print Trivial_boolToInt.

  
  Print Trivial_boolToIntTracker_opt.
  Print Trivial_boolToIntTracker.

  Lemma boolToInt_proof : forall input context before result after HContext1 HContext2 HContext3,
    let machine_environment :=
      (make_machine_env contract_address before context (fun _ _ _ _ => true) HContext1 HContext2 HContext3) in

    runStateT (Trivial_boolToInt_opt input machine_environment) (contract_state before)
      = Some (result, after)
    
    ->
    
    result = 1 <-> input = true.

  Proof. (* .all -.h#memModelOps *)
    intros. (* .all -.h#machine_environment -.h#memModelOps *)
    Transparent Trivial_boolToInt_opt. (* .all -.h#* .h#H *)
    unfold Trivial_boolToInt_opt in H. (* .all -.h#* .h#H *)
    split; intros. (* .all -.h#* *)
      - (* "->" result is 1 ∴ input is true. *) (* .all -.h#* .h#H .h#H0 *)
        inv_runStateT_branching. (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
        + (* Go down true branch of if statement. *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
          reflexivity.
        + (* Go down false branch of if statement, gives a contradiction. *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
          subst. (* .all -.h#* .h#H1 *) discriminate.
      - (* "<-" input is true ∴ result is 1. *)  (* .all -.h#* .h#H .h#H0 *)
        inv_runStateT_branching. (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
        + (* Go down true branch of if statement *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
          subst. (* .all -.h#* .h#H0 *)  reflexivity.
        + (* Go down false branch of if statement, gives a contradiction. *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
          discriminate.
  Qed.

  Lemma boolToIntTracker_proof : forall input context before result after HContext1 HContext2 HContext3,
  let machine_environment :=
  (make_machine_env contract_address before context (fun _ _ _ _ => true) HContext1 HContext2 HContext3) in
    runStateT (Trivial_boolToIntTracker_opt input machine_environment) (contract_state before)
      = Some (result, after)
    -> result = 1 <-> input = true. (* .all -.h#memModelOps *)
  Proof. (* .all -.h#memModelOps *)
    intros. (* .all -.h#machine_environment -.h#memModelOps *)
    Transparent Trivial_boolToIntTracker_opt. (* .all -.h#* .h#H *)
    unfold Trivial_boolToIntTracker_opt in H. (* .all -.h#* .h#H *)
    split; intros. (* .all -.h#* *)
      - (* "->" result is 1 ∴ input is true. *) (* .all -.h#* .h#H .h#H0 *)
        inv_runStateT_branching. (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H3 .h#H4 *)
        + (* Go down true branch of if statement. *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H3 .h#H4 *)
          reflexivity.
        + (* Go down false branch of if statement, gives a contradiction. *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
          subst. (* .all -.h#* .h#H1 *) discriminate.
      - (* "<-" input is true ∴ result is 1. *)  (* .all -.h#* .h#H .h#H0 *)
        inv_runStateT_branching. (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H3 .h#H4 *)
        + (* Go down true branch of if statement *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H3 .h#H4 *)
          subst. (* .all -.h#* .h#H0 *)  reflexivity.
        + (* Go down false branch of if statement, gives a contradiction. *) (* .all -.h#* .h#Heqb .h#H0 .h#H1 .h#H2 *)
          discriminate.
  Qed.


  Require Import Crowdfunding.DataTypeOps.
  Require Import Crowdfunding.LayerCONTRACT.
  Require Import Crowdfunding.ContractModel.
  Import Crowdfunding.ContractModel.ContractModel.

  Section ProofCrowdfunding.

  Definition wei := int256. (* TODO consider whether this should be a tagged type instead. *)
  Delimit Scope int256_scope with int256.
  Infix "+" := Int256.add : int256_scope.
  Infix "-" := Int256.sub : int256_scope.
  Infix "=?" := Int256.eq (at level 70, no associativity) : int256_scope.

  Ltac me_transfer_cases :=
    try match goal with
      H : (Int256.one =? Int256.one)%int256 = false |- _ => 
        rewrite Int256.eq_true in H; discriminate
        end;
    try match goal with
      H : runStateT mzero _ = ret _ |- _ => 
      simpl in H; discriminate
    end.

  (* TODO this will probably need updating based on the definition of me_transfer *)
  Ltac ds_inv :=
        repeat (
          try inv_runStateT_branching;
          let Case := fresh "NoOverflowOrUnderflowInTransferCase" in
          try match goal with
            | H : context[me_transfer _  _ _] |- _ => 
            unfold me_transfer, make_machine_env in H;
            destruct (noOverflowOrUnderflowInTransfer _ _ _ _
                      && (_ _ _ _ _)) eqn:Case
          end
        );
        me_transfer_cases.

  

  (*
  The goal here is to, in a sense, quantify over an arbitrary snapshot of the Blockchain and then model all possible interactions after that point. In particular, modelling most precisely the smart contract.
  *)

  Section Blockchain_Model.

  (* begin snippet snapshot_variables *)
  Context
    (snapshot_timestamp : int256)
    (snapshot_number : int256)
    (snapshot_blockhash : int256 -> int256)
    (snapshot_balances : addr -> ContractModel.wei).
  (* end snippet snapshot_variables *)

  Definition ContractState := global_abstract_data_type.

  (* begin snippet initial_state *)
  Definition initial_state : BlockchainState :=
    mkBlockchainState
      snapshot_timestamp
      snapshot_number
      snapshot_balances
      snapshot_blockhash
      init_global_abstract_data
  .
  (* end snippet initial_state *)

  Context {HmemOps: MemoryModelOps mem}.
  
  
  (* begin snippet assumption_example *)
  Context
    (address_accepts_funds :
      option ContractState -> addr -> addr -> wei -> bool).
  Open Scope int256. (* .none *)
  Definition address_accepts_funds_assumed_for_from_contract 
    d sender recipient amount :=
    if sender =? contract_address then true else
    address_accepts_funds d sender recipient amount.
  Check address_accepts_funds_assumed_for_from_contract.
  Close Scope int256. (* .none *)
  Definition address_accepts_funds_assumption :=
    address_accepts_funds_assumed_for_from_contract.
  (* end snippet assumption_example *)

  (* The current model also has the implicit assumption that the transfers to a smart contract during a function call via callvalue are always accepted by the contract.
    This could be changed by editing callvalue_prf in the definition of Action, similarly to how it is done for `externalBalanceTransfer` *)

  Definition updateTimeAndBlock before block_count time_passing : BlockchainState :=
  mkBlockchainState
    (time_passing + (timestamp before))%int256
    (block_count + (block_number before))%int256
    (balance before)
    (blockhash before)
    (contract_state before)
  .

  Definition validTimeChange block_count time_passing current_block_number current_timestamp : bool :=
    (* Note, testing for positive block_count and time_passing is unnecessary while they are Int256 values.
      It would be necessary to add positivity checks if using Z instead of course. *)
    ((Int256.intval block_count) + (Int256.intval current_block_number) <=? Int256.max_unsigned)%Z
    && ((Int256.intval time_passing) + (Int256.intval current_timestamp) <=? Int256.max_unsigned)%Z.

  Open Scope int256.
  Definition update_balances sender recipient amount balances : (addr -> wei) :=
    (* Here the balances are updated without checking for overflows. Overflow checks must be done elsewhere. *)
    fun a => 
    if sender =? recipient then balances a else
      if a =? sender then (balances sender) - amount else
      if a =? recipient then (balances recipient) + amount
        else balances a.
  Close Scope int256.

  Definition update_balance before latest_balances : BlockchainState :=
    mkBlockchainState
    (timestamp before)
    (block_number before)
    latest_balances
    (blockhash before)
    (contract_state before)
  .

  Definition noOverflowOrUnderflowInTransfer (sender recipient : addr) (amount : wei) (balances : addr -> wei) : bool := 
    ((Int256.intval (balances sender)) - (Int256.intval amount) >=? 0)%Z
    && ((Int256.intval (balances recipient)) + (Int256.intval amount) <=? Int256.max_unsigned)%Z.

  (* TODO-Review - This defines how balances are updated in the model after transferEth *)
  Open Scope int256.
  Definition current_balances 
    (* Note on where insufficient balance-checking takes place:
      Overflow and underflow of balances must already have been checked before this function.
      (i.e. before a transfer is placed in Outgoing_transfer_recipient_and_amount it should
            have been checked to ensure no overflow/underflow.)
      Currently this check is expected to be implemented by the me_transfer definition.
      !! Ensure you are using an appropriate me_transfer definition. !! *)
    (successful_transfer : option (addr * wei))
    (initial_balances : addr -> wei) 
    : (addr -> wei) :=
      match successful_transfer with
        | None => initial_balances
        | Some (recipient, amount) => 
            update_balances contract_address recipient amount initial_balances
      end.
  Close Scope int256.

  Definition new_balance_after_contract_call (before : BlockchainState) (d : ContractState) : (addr -> wei) :=
      (current_balances
        (Outgoing_transfer_recipient_and_amount d)
        (balance before)).

  Definition next_blockchain_state (before : BlockchainState) (d : ContractState) : BlockchainState :=
    mkBlockchainState
      (timestamp before)
      (block_number before)
      (new_balance_after_contract_call before d)
      (blockhash before)
      d.

  (* This approach to defining Action requires all calls to a contract
    function to succeed, i.e. return (Some _ _), failure cases are
    amalgamated into the revert case. This means only needing to prove
    the (typically) trivial revert case once, without losing generality. *)
  Inductive Action (before : BlockchainState) :=
    | call_Crowdfunding_donate (context : CallContext)
        (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
        r (* The return value of calling donate successfully given the context (and arguments, if applicable) *)
        contract_state_after (* The contract state after calling donate successfully given the context (and arguments, if applicable) *)
        (case_donate_prf : 
            runStateT (Crowdfunding_donate_opt (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
            = Some (r, contract_state_after))
    | call_Crowdfunding_getFunds (context : CallContext)
        (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
        r (* The return value of calling getFunds successfully given the context (and arguments, if applicable) *)
        contract_state_after (* The contract state after calling getFunds successfully given the context (and arguments, if applicable) *)
        (case_getFunds_prf : 
            runStateT (Crowdfunding_getFunds_opt (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
            = Some (r, contract_state_after))
    | call_Crowdfunding_claim (context : CallContext)
        (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context) contract_address (callvalue context) (balance before) = true)
        r (* The return value of calling claim successfully given the context (and arguments, if applicable) *)
        contract_state_after (* The contract state after calling claim successfully given the context (and arguments, if applicable) *)
        (case_claim_prf : 
            runStateT (Crowdfunding_claim_opt (make_machine_env contract_address before context address_accepts_funds_assumption)) (contract_state before)
            = Some (r, contract_state_after))
    | externalBalanceTransfer (sender recipient : addr) (amount : wei) (* Note that if wei is currently an int256, so it is guaranteed to be non-negative. If ever changed to using Z again an appropriate check would be needed in this definition. *)
        (prf : sender <> contract_address /\ 
          ((noOverflowOrUnderflowInTransfer sender recipient amount (balance before))
          && (address_accepts_funds_assumption None sender recipient amount) = true))
    | timePassing (block_count time_passing : int256)
                  (prf : validTimeChange block_count time_passing (block_number before) (timestamp before) = true)
    | revert (* A no-op, or a call with some error resulting in no state change, such as a contract reverting during its code execution, or such as calling an invalid function when there is no fallback defined. TODO check that DeepSEA does not have any fallback function in generated bytecode. *).

.. coq:: none

  Fixpoint step
    (before : BlockchainState) (action : Action before) : BlockchainState :=
  match action with
  | call_Crowdfunding_donate context
      callvalue_prf r d_after case_donate_prf => 
        next_blockchain_state before d_after
  | call_Crowdfunding_claim context
      callvalue_prf r d_after case_claim_prf => 
        next_blockchain_state before d_after
  | call_Crowdfunding_getFunds context
      callvalue_prf r d_after case_getFunds_prf => 
        next_blockchain_state before d_after
  | timePassing block_count time_passing prf => 
      updateTimeAndBlock before block_count time_passing
  | externalBalanceTransfer sender recipient amount prf =>
      update_balance before (update_balances sender recipient amount (balance before))
  | revert => before
  end.

.. coq:: none

  Definition resetTransfers (d : ContractState) : ContractState :=
    {|
    Crowdfunding_owner := Crowdfunding_owner d;
    Crowdfunding_max_block := Crowdfunding_max_block d;
    Crowdfunding_goal := Crowdfunding_goal d;
    Crowdfunding_backers := Crowdfunding_backers d;
    Crowdfunding_funded := Crowdfunding_funded d;
    Crowdfunding_deadlinePassed_msg := Crowdfunding_deadlinePassed_msg d;
    Crowdfunding_successfullyDonated_msg := Crowdfunding_successfullyDonated_msg d;
    Crowdfunding_alreadyDonated_msg := Crowdfunding_alreadyDonated_msg d;
    Crowdfunding_funded_msg := Crowdfunding_funded_msg d;
    Crowdfunding_failed_msg := Crowdfunding_failed_msg d;
    Crowdfunding_too_early_to_claim_funds_msg := Crowdfunding_too_early_to_claim_funds_msg d;
    Crowdfunding_too_early_to_reclaim_msg := Crowdfunding_too_early_to_reclaim_msg d;
    Crowdfunding_cannot_refund_msg := Crowdfunding_cannot_refund_msg d;
    Crowdfunding_here_is_your_money_msg := Crowdfunding_here_is_your_money_msg d;
    Outgoing_transfer_recipient_and_amount := None
  |}.

.. coq:: none

  Record Step := mkStep
    {
      Step_state : BlockchainState;
      Step_action : Action Step_state
    }.

.. coq:: none

  Record StepSpace := mkStepSpace
    {
      StepSpace_state : BlockchainState;
      StepSpace_actions : Type
    }.

  Class Next (b : BlockchainState) : Type :=
  {
      next : Action b -> BlockchainState
  }.

  Instance : Next initial_state :=
  {
    next := step initial_state
  }.


  Definition InSecond (st : BlockchainState) := 
    exists (a : Action initial_state), st = step initial_state a.

  Definition InThird (st : BlockchainState) := 
      exists (two : BlockchainState) (a : Action two) ,
        InSecond two /\ st = step two a.

  Definition InFourth (st : BlockchainState) := 
    exists (three : BlockchainState) (a : Action three) ,
      InThird three /\ st = step three a.

  Open Scope nat.
  Inductive InPossible (st : BlockchainState) (n:nat) :=
    | inzero (H : exists (a : Action initial_state), st = step initial_state a) (Hn : n = 0) : InPossible st n
    | inSn (current : BlockchainState) (Hs : InPossible current (n - 1)) 
    
    (
      H : exists (a : Action current),
      st = step current a
    )
    : InPossible st n
    
    .
  Close Scope nat.

  Definition stepOnce prev := (step (Step_state prev) (Step_action prev)).
  Definition stepOnceAndWrap prev next_action := (mkStep (stepOnce prev) next_action).
  Hint Unfold stepOnce stepOnceAndWrap.

  (* begin snippet ReachableVia *)


.. coq:: none

  Inductive ReachableVia from :
    BlockchainState -> Step-> list Step -> Prop :=
  | initial_case (next_action : Action from)
      : ReachableVia from from
                        (mkStep from next_action)
                        [mkStep from next_action]
  | step_case 
      (prevSt : BlockchainState) (prev : Step)
      (prevList : list Step)
      (Hprev : ReachableVia from prevSt
                              prev prevList)
      (next_action : Action (stepOnce prev))
      : ReachableVia from  (stepOnce prev) 
      (stepOnceAndWrap prev next_action)
      (stepOnceAndWrap prev next_action
          :: prevList).

.. coq:: none

  (* end snippet ReachableVia *)
  (* begin snippet ReachableViaLinkStateToStep *)
  Lemma ReachableViaLinkStateToStep : forall st st' s l,
    ReachableVia st st' s l -> st' = Step_state s.
  Proof.
    intros.
    destruct H; reflexivity.
  Qed.
  (* end snippet ReachableViaLinkStateToStep *)

  Lemma ReachableViaLinkStepToList : forall st st' s l,
    ReachableVia st st' s l -> exists tl, s :: tl = l.
  Proof.
    intros.
    destruct H.
    - exists []. reflexivity.
    - exists prevList. reflexivity.
  Qed.

  Ltac reachableFromByLinks := 
    match goal with
    | H : ReachableVia _ _ _ _ |- _ => 
      let StateToStepName := fresh "HReachableViaLinkStateToStep" in
      let StepToListName := fresh "HReachableViaLinkStepToList" in
      epose proof (ReachableViaLinkStateToStep _ _ _ _ H) as StateToStepName;
      epose proof (ReachableViaLinkStepToList _ _ _ _ H) as StepToListName
    end.


  (* Ugh *)
  (* Inductive ReachableVia from (s : BlockchainState) (next_action : Action s) : list Step -> Prop :=
  | initial_case (first_action : Action from)
      : ReachableVia from from first_action [mkStep from first_action]
  | step_case (prevList : list Step) (Hprev : ReachableVia from s next_action prevList)
      (next_step_action : Action (step s next_action))
      : ReachableVia from (step s next_action) next_step_action
      (stepOnce s next_action next_step_action :: prevList)  
  . *)

  Definition ReachableFrom from state := exists l step', ReachableVia from state step' l.

  Definition Reachable := ReachableFrom initial_state.

  (* begin snippet since_as_long:: no-out *)

===================================
A Crowdfunding Correctness Property
===================================

----

.. coq:: fold

  Definition since_as_long (Property1 : BlockchainState -> Prop)
      (Property2 : BlockchainState -> Prop) (PropertyAboutAction : Step -> Prop) :=
    forall actions start finish helper,
      ReachableVia start finish helper actions ->
      Property1 start
      -> (forall act, List.In act actions -> PropertyAboutAction act)
      -> Property2 finish.

  Notation "Property2 `since` Property1 `as-long-as` PropertyAboutAction" :=
    (since_as_long Property1 Property2 PropertyAboutAction) (at level 1).

.. coq:: none

  (* end snippet since_as_long *)

  (* begin snippet donation_recorded *)
  Definition donation_recorded (a : addr)
    (amount : Z) (s : BlockchainState) :=
      Int256Tree.get_default 0 a
        (Crowdfunding_backers (contract_state s))
          > 0.
  (* end snippet donation_recorded *)

  Definition no_claims_from (a : addr) (s : Step) :=
    match Step_action s with
    | (call_Crowdfunding_claim _ a _ _ _) => False
    | _ => True
    end.
      
  Ltac destruct_if_H :=
    let caseName := fresh "IfCase" in
    match goal with
      | [ _ : context[if ?X then _ else _] |- _ ] => destruct X eqn:caseName
    end.

  Ltac destruct_beq256_H :=
    let caseName := fresh "IfCaseBeq" in
      match goal with
        | [ _ : context[(?X =? ?Y)%int256] |- _ ] => destruct (X =? Y)%int256 eqn:caseName
      end.

  Ltac destruct_geq256_H :=
    let caseName := fresh "IfCaseGeq" in
      match goal with
        | [ _ : context[(?X >=? ?Y)%int256] |- _ ] => destruct (X >=? Y)%int256 eqn:caseName
      end.

  Hint Unfold Z_bounded. (*Causes annoying issues, use autounfold in *. *)
    

  Ltac destruct_and :=
    match goal with
      | [ H : (_ /\ _) |- _ ] => destruct H
    end.

----

.. coq:: none

  Ltac Hlinks := 
  match goal with
  | H : ReachableVia _ _ _ _ |- _ => 
    let StateToStepName := fresh "HS" in
    let StepToListName := fresh "HL" in
    epose proof (ReachableViaLinkStateToStep _ _ _ _ H) as StateToStepName;
    epose proof (ReachableViaLinkStepToList _ _ _ _ H) as StepToListName
  end.

  Ltac inv_FT :=
    try match goal with H : false = true |- _ => inversion H end.

  Hint Unfold stepOnceAndWrap step stepOnce make_machine_env.

  Definition donate_fun := Crowdfunding_donate_opt.


.. coq:: fold

  Open Scope int256. (* .none *)

  Theorem donation_preserved :
    forall (user : addr) (amount : Z),
                   (donation_recorded user amount) 
      `since`      (donation_recorded user amount)
      `as-long-as` (no_claims_from user).

----

.. coq:: fold

  Proof.
  unfold since_as_long.
  intros.
  
  induction H; [assumption|].
  
  assert(donation_recorded user amount prevSt).
  apply IHReachableVia.
  intros.
  apply H1.
  apply in_cons; assumption.

  clear H0.
  clear IHReachableVia.
  unfold donation_recorded in *.

  reachableFromByLinks.

  assert (no_claims_from user prev).
  apply H1.
  destruct HReachableViaLinkStepToList.
  subst.
  right. left. reflexivity.

  destruct prev; simpl in *; unfold stepOnceAndWrap, step in *; simpl in *.
  clear H1. (* no_claims_one, not needed this time? *)
  clear next_action.
  clear H. (* ReachableVia, no longer needed? *)
  clear HReachableViaLinkStepToList.
  unfold no_claims_from in H0.
  unfold stepOnce. simpl.
  unfold donation_recorded in *.
  destruct Step_action0; simpl in *;
    rewrite <- HReachableViaLinkStateToStep in *;
    clear HReachableViaLinkStateToStep Step_state0.
    - Transparent Crowdfunding_donate_opt. unfold Crowdfunding_donate_opt in case_donate_prf.
      ds_inv; subst; simpl.
      + match goal with H : false = true |- _ => inversion H end.
      + destruct (user =? (caller context))%int256 eqn:Case.
        * apply Int256eq_true in Case. rewrite <- Case.
          rewrite get_default_ss.
          exfalso.
          subst.
          unfold make_machine_env in Heqb0; simpl in Heqb0.
          apply Z.eqb_eq in Heqb0.
          rewrite Heqb0 in H2.
          lia.
        * apply Int256eq_false in Case.
          rewrite get_default_so; assumption.
      + match goal with H : false = true |- _ => inversion H end.
    - Transparent Crowdfunding_getFunds_opt. unfold Crowdfunding_getFunds_opt in case_getFunds_prf.
      ds_inv; subst; simpl; try lia.
    - contradiction.
    - assumption.
    - assumption.
    - assumption.
  Qed.
  

  Close Scope int256. (* .none *)

.. note::

  If showing a part of this, show the very last Transparent and unfold of getFunds_opt.
  This shows something familiar that looks complex but is resolved via automation, because getFunds is what is called by the owner, so it has no bearing on the user donation record which is the focus of this lemma.
  
  Also can show the first section, in particular after "Proof."

.. coq:: none

  End Blockchain_Model.
  End ProofCrowdfunding.

----

===============
Paper overviews
===============

----

.. image:: modelling-a-blockchain-paper.png
  :target: https://academic.danielb.space/#/page/Publications

----

.. image:: provably-correct-paper.png
  :target: https://academic.danielb.space/#/page/Publications

----

.. image:: reentrancy-paper.png
  :target: https://academic.danielb.space/#/page/Publications

----

.. image:: amm-paper.png
  :target: https://drops.dagstuhl.de/opus/volltexte/2021/15425/pdf/OASIcs-FMBC-2021-1.pdf

----

.. image:: deepsea-paper.png
  :target: https://dl.acm.org/doi/pdf/10.1145/3360562

----

**References**

- Slides_ powered by Alectryon_: https://github.com/cpitclaudel/alectryon
- The DeepSEA compiler is partly based upon the CompCert_ Verified Compiler
- My papers: https://academic.danielb.space (Get in touch here)
- C DeepSEA paper: https://dl.acm.org/doi/pdf/10.1145/3360562
- Verified Price Oracles paper: https://doi.org/10.4230/OASIcs.FMBC.2021.1

- GitHub links:
    - DeepSEA_
    - My DeepSEA fork_ 
    - The Crowdfunding_ contract (as for the FTSCS paper)

.. _Slides: https://github.com/Coda-Coda/Alectryon-slides/tree/eth-eng-grp-talk-2023
.. _Alectryon: https://github.com/cpitclaudel/alectryon
.. _CompCert: https://compcert.org/
.. _DeepSEA: https://github.com/ShentuChain/deepsea
.. _fork: https://github.com/Coda-Coda/deepsea-1
.. _Crowdfunding: https://github.com/Coda-Coda/Crowdfunding/tree/FTSCS-2022

----

**Thank you!**

*I would like to thank my supervisor Professor Steve Reeves at the University of Waikato and Vilhelm Sjöberg at CertiK for their valuable insights and input.*

*I would also like to thank Associate Professor Jing Sun and the University of Auckland for kindly hosting me during this research.*

----

=================
Additional Slides
=================

----

=================================================
Example: a property of a list membership function
=================================================

----

.. coq:: none

  Require Import Nat.
  Require Import PeanoNat.
  Require Import Bool.
  Require Import List.
  Import ListNotations.

.. coq:: fold

  Module MyList. (* .none *)
  Inductive list (A : Type) : Type :=
  | nil : list A 
  | cons : A -> list A -> list A.
  End MyList. (* .none *)

  Fixpoint contains (n:nat) (l:list nat) : bool :=
    match l with
    | [] => false
    | h :: tl => (n =? h) || contains n tl
  end.

----

.. coq:: fold

  Lemma contains_property :
    forall n list1, contains n list1 = true
      -> forall list2, contains n (list1 ++ list2) = true.
  Proof.
    intros n.  
    induction list1.
    - simpl. intros. discriminate.
    - intros. simpl in *.
      apply orb_prop in H.
      destruct H.
      + apply orb_true_intro.
        left. assumption.
      + apply orb_true_intro.
        right.
        eapply IHlist1 in H.
        eassumption. 
  Qed.

----

.. coq:: fold

  Lemma contains_correctness : forall n l, contains n l = true <-> In n l.
  Proof.
    Print In.
    split.
    - induction l as [|l'].
      + simpl. discriminate.
      + simpl. intros.
        apply orb_prop in H.
        destruct H.
        * left. rewrite Nat.eqb_eq in H. auto.
        * right. apply IHl in H. assumption.
    - induction l as [|l'].
      + simpl. contradiction.
      + simpl. intros.
        destruct H.
        * apply orb_true_intro.
          left.
          subst.
          apply Nat.eqb_refl.
        * apply orb_true_intro.
          right.
          auto.
  Qed.

----

=============================
Example: Simple state machine
=============================

----

.. image:: fsm-diagram-transparent.png
   :alt: example state machine diagram

----

.. coq:: none

  Require Import Coq.Program.Tactics.
  Local Obligation Tactic := idtac.
  Module fsm.

.. coq:: fold

  Inductive State :=
    | initial
    | middle
    | extra
    | final
  .

  Inductive Transition (before : State) :=
    | advance (prf : before <> final)
    | sidetrack (prf : before = initial).

----

.. coq:: fold

  Local Obligation Tactic := try discriminate. (* .none *)
  Program Definition step (s : State) (t : Transition s) :=
    match t with
    | advance _ =>
      match s with
      | initial => middle
      | middle => final
      | extra => middle
      | final => _
      end
    | sidetrack _ =>
      match s with
      | initial => extra
      | _ => _
      end
  end.

----

.. coq:: fold

  Next Obligation.
  intros.
  exfalso.
  subst.
  contradiction.
  Defined.
  Next Obligation.
  intros.
  exfalso.
  subst.
  contradiction.
  Defined.

.. code:: coq

  Local Obligation Tactic := try discriminate. (* Used for the above. *)

----

.. coq:: fold

  Lemma three_transitions_gives_final : 
  forall t1 t2 t3, let s1 := step initial t1 in let s2 := step s1 t2 in
    step s2 t3 = final.
  Proof.
  intros.
  destruct t1. simpl in *.
    - destruct t2. simpl in *.
      + destruct t3.
        * contradiction.
        * discriminate.
      + discriminate. 
    - destruct t2. simpl in *.
      + destruct t3. simpl in *.
        * reflexivity.
        * discriminate.
      + discriminate.
  Qed.

  End fsm. (* .none *)