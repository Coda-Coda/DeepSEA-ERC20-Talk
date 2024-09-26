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

  Lemma boolToInt_proof' : forall input context before result after HContext1 HContext2 HContext3,
    let machine_environment :=
      (make_machine_env contract_address before context (fun _ _ _ _ => true) HContext1 HContext2 HContext3) in

    runStateT (Trivial_boolToInt_opt input machine_environment) (contract_state before)
      = Some (result, after)
    
    ->
    
    result = 1 <-> input = true.
  Proof.
    intros.
    Transparent Trivial_boolToInt_opt. unfold Trivial_boolToInt_opt in H.
    split; inv_runStateT_branching; try subst; try discriminate; try reflexivity.
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

End Proof.

(**
%
Having explored correctness proofs for properties of a crowdfunding smart contract, we now explore an ERC-20~\cite{erc20} wrapped ether smart contract that implements a fungible token inherently pegged to the value of ether at a 1:1 ratio. Fungible tokens correspond to values of varying quantity, unlike non-fungible tokens (NFTs) which correspond to unique, non-countable items. Anyone can send ether to this fungible token smart contract (`minting' the token) and the amount of ether they sent will be set aside for the user to withdraw at a later stage (`burning' the token). The user can also transfer their wrapped ether to someone else as well as permit a third party to transfer some amount of their wrapped tokens on their behalf, in line with the ERC-20 specification~\cite{erc20}. This token is written to be compliant with the ERC-20 specification, and some properties described or implied by the standard have been proved to hold. The implementation of this smart contract and its proofs could be adapted to create custom ERC-20 tokens without needing to redo most of the proof effort.

We will explore five proofs, the first similar to the preservation of the donation record from the crowdfunding smart contract. Here, we will prove that once ether has been wrapped, if there are no transfers or burning of the token, then the user retains at least that much wrapped ether. Secondly, we will prove a property about the transfer function alone, to demonstrate how one can phrase a property directly about a single smart contract function \emph{without} making use of the blockchain model introduced in \Cref{sec:Modelling}. The remaining three proofs are safety properties and bear similarities to the proof of the sufficient balance theorem of the crowdfunding smart contract.
%
*)

(** * Contract Source Code *)

(** 
%
\input{"../theories/ERC20WrappedEth/proofs/ERC20WrappedEthds-1.tex"}
%
*)

(* begin hide *)
Require Import ERC20WrappedEth.DataTypeOps.
Require Import ERC20WrappedEth.LayerCONTRACT.

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

Require Import ERC20WrappedEth.DataTypes.
Require Import backend.MachineModel.

Import ListNotations.

Require Import core.MemoryModel. 
Require Import HyperTypeInst.

Require Import Maps.
Import Maps.Int256Tree_Properties.
Import Maps.Int256Tree. 

Require Import ERC20WrappedEth.ContractModel.
Import ERC20WrappedEth.ContractModel.ContractModel.

Ltac abbreviated := idtac.

Open Scope Z.

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

Section GenericProofs.
Lemma fold_snd_map : 
  forall  A B (m : list (A * B)) x f,
  (fold_left (fun (a : B) (p : A * B) => f a (snd p))
   m x) = 
  (fold_left f
  (List.map snd m) x).
Proof.
    intro.
    induction m.
    - intros. simpl. reflexivity.
    - intros. simpl. rewrite IHm. reflexivity.
Qed. 


Lemma sum_starting_from_init_equals_sum_plus_init_arbitrary_start : 
forall (x init : Z) (m : Int256Tree.t Z),
Int256Tree.fold1 Z.add m (init + x) = Z.add (Int256Tree.fold1 Z.add m x) init.
Proof.
  intros.
  repeat rewrite Int256Tree.fold1_spec.
  assert(
  forall x,
    (fold_left (fun (a : Z) (p : Int256Tree.elt * Z) => Z.add a (snd p))
    (Int256Tree.elements m) x) = 
    (fold_left Z.add
    (List.map snd (Int256Tree.elements m)) x)).
    {
      intros.
      apply fold_snd_map.
    }
  repeat rewrite H. clear H.
  rewrite <- fold_left_last.
  repeat rewrite fold_symmetric; try (intros; lia).
  remember (List.map snd (Int256Tree.elements m)) as l.
  clear Heql. clear m. generalize dependent l.
  induction l.
    - simpl. lia.
    - simpl.
    rewrite IHl.
    reflexivity.
Qed.


Lemma sum_starting_from_init_equals_sum_plus_init : 
forall (init : Z) (m : Int256Tree.t Z),
Int256Tree.fold1 Z.add m init = Z.add (Int256Tree.fold1 Z.add m 0) init.
Proof.
  intros.
  rewrite <- sum_starting_from_init_equals_sum_plus_init_arbitrary_start.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma Int256Tree_sum_set_value_initially_zero : 
  forall (m: Int256Tree.t Z32)  k v, Int256Tree.get_default 0 k m = 0
                -> Int256Tree_Properties.sum (Int256Tree.set k v m) = 
                   Int256Tree_Properties.sum m + v.
Proof.
  unfold Z32.
  intros.
  pose (@Int256Tree_Properties.sum_get_default 0 k v (Int256Tree.set k v m)) as Lemma1.
  simpl in Lemma1.
  unfold Int256Tree_Properties.sum.
  rewrite Lemma1; [|  unfold Int256Tree.get_default;
                      rewrite Int256Tree.gss;
                      reflexivity].
  rewrite Int256Tree_Properties.fold1_remove_set; [|intros; lia].
  unfold Int256Tree.get_default in H.

  destruct (Int256Tree.get k m) eqn:Case.
  - rewrite H in Case.
     assert(Zswap : forall x y a : Z, a + x + y = a + y + x) by (intros; lia).
     epose (Int256Tree_Properties.fold1_get Z.add Zswap v Case) as H0.
     rewrite Z.add_0_r in H0.
     rewrite <- H0.
     pose Int256Tree_Properties.sum_extensional.
     apply sum_starting_from_init_equals_sum_plus_init.
   - 
   assert(Int256Tree.get_default 0 k m = 0).
   unfold Int256Tree.get_default.
   rewrite Case. reflexivity. 
   pose (@Int256Tree_Properties.sum_get_default v k 0 m H0).
   rewrite Z.add_0_r in e.
   rewrite <- e.
   apply sum_starting_from_init_equals_sum_plus_init.
Qed.

Lemma sum_set_y_remove_from_starting_x : 
  forall k m x y,
  Int256Tree.fold1 Z.add (Int256Tree.set k y m) x =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) x + y.
Proof.
  intros.
  pose (Int256Tree.grs k m).
  pose (Int256Tree_Properties.set_permutation 0 e).
  rewrite <- Int256Tree_Properties.elements_set_decompose in p.
  rewrite fold1_set by lia.
  (* assert (x + 0 = x) by apply Z.add_0_r.
  rewrite <- H at 2. *)
  rewrite sum_starting_from_init_equals_sum_plus_init.
  symmetry.
  rewrite sum_starting_from_init_equals_sum_plus_init.
  rewrite Z.add_assoc.
  reflexivity.
Qed.

Lemma sum_set_zero_remove_from_starting_x : 
  forall k m x,
  Int256Tree.fold1 Z.add (Int256Tree.set k 0 m) x =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) x.
Proof.
  intros.
  rewrite sum_set_y_remove_from_starting_x.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma sum_set_zero_remove : 
  forall k m,
  Int256Tree.fold1 Z.add (Int256Tree.set k 0 m) 0 =
  Int256Tree.fold1 Z.add (Int256Tree.remove k m) 0.
Proof.
  intros.
  apply sum_set_zero_remove_from_starting_x.
Qed.

Lemma sum_set_x_minus_from_arbitrary_init : 
  forall (k : elt) (m : t Z) (v x init : Z),
  get_default 0 k m = v ->
  fold1 Z.add (set k x m) init = fold1 Z.add m init + (x - v).
Proof.
unfold sum.
  intros.
  unfold Int256Tree_Properties.sum.
  unfold Int256Tree.get_default in H.
  destruct (Int256Tree.get k m) eqn:Case.
    - subst.
      assert((forall x y a : Z, a + x + y = a + y + x)) by (intros; lia).
      epose (Int256Tree_Properties.fold1_get Z.add H init Case).
      rewrite e.
      simpl.
      assert (init + v = v + init) by apply Z.add_comm.
      rewrite H0. clear H0.
      rewrite (sum_starting_from_init_equals_sum_plus_init_arbitrary_start init).
      rewrite sum_set_y_remove_from_starting_x.
      lia.
    - subst.
      assert((forall x y a : Z, a + x + y = a + y + x)) by (intros; lia).
      (* epose (Int256Tree_Properties.fold1_get Z.add H init Case). *)
      (* rewrite e. *)
      simpl.
      rewrite Z.sub_0_r.
      rewrite sum_set_y_remove_from_starting_x.
      (** For upcoming pose proof *)
      assert(get_default 0 k m = 0). unfold get_default. rewrite Case. reflexivity.
      pose proof (@sum_get_default init k 0 m H0).
      rewrite Z.add_0_r in H1.
      rewrite <- H1.
      reflexivity.
Qed.

Lemma sum_set_zero_minus_from_arbitrary_init : 
  forall (k : elt) (m : t Z) (v init : Z),
  get_default 0 k m = v ->
  fold1 Z.add (set k 0 m) init = fold1 Z.add m init - v
.
Proof.
intros.
apply sum_set_x_minus_from_arbitrary_init; assumption.
Qed.

Lemma sum_set_zero_minus : forall k m v, Int256Tree.get_default 0 k m = v ->
Int256Tree_Properties.sum (Int256Tree.set k 0 m) = Int256Tree_Properties.sum m - v.
Proof.
  intros.
  unfold sum.
  apply sum_set_zero_minus_from_arbitrary_init.
  assumption.
Qed.

Lemma Int256Tree_sum_minus_equality : 
  forall m k x,
    Int256Tree_Properties.sum m >= x
    ->
    Int256Tree_Properties.sum (Int256Tree.set k 0 m) =
    (Int256Tree_Properties.sum m) - (Int256Tree.get_default 0 k m).
Proof.
intros.
unfold sum.
rewrite sum_set_zero_minus_from_arbitrary_init with (v:= Int256Tree.get_default 0 k m) by reflexivity.
reflexivity.
Qed.

Lemma Int256Tree_sum_minus_from_starting_x :
  forall (m : t Z) (k : elt) (x : Z),
      fold1 Z.add (set k 0 m) x =
      fold1 Z.add m x - get_default 0 k m.
Proof.
  intros.
  rewrite sum_set_zero_minus_from_arbitrary_init with (v:= Int256Tree.get_default 0 k m) by reflexivity.
  reflexivity.
Qed.

Lemma Int256Tree_sum_minus : 
  forall m k x,
    Int256Tree_Properties.sum m <= x
    ->
    Int256Tree_Properties.sum (Int256Tree.set k 0 m) <=
    x - (Int256Tree.get_default 0 k m).
Proof.
intros.
rewrite sum_set_zero_minus with (v:= Int256Tree.get_default 0 k m) by reflexivity.
lia.
Qed.

End GenericProofs.

Module FunctionalCorrectness.

(*
The goal here is to, in a sense, quantify over an arbitrary snapshot of the Blockchain and then model all possible interactions after that point. In particular, modelling most precisely the smart contract.
*)

Section Blockchain_Model.

Open Scope int256.

Context
  (snapshot_timestamp : int256)
  (snapshot_number : int256)
  (snapshot_blockhash : int256 -> int256)
  (snapshot_balances : addr -> wei). (* This also guarantees balances are non-negative. *)

Context
  (snapshot_balances_valid_prf : forall a, 0 <= (snapshot_balances a) < Int256.modulus).

Context
  (contract_address : addr).

Definition ContractState := global_abstract_data_type.

Context
  (address_accepts_funds : option ContractState -> addr -> addr -> wei -> bool).
(* The following is a helpful alternative to suppose instead of using `address_accepts_funds` alone. But it must be assumed explicitly. *)
Definition address_accepts_funds_assumed_for_from_contract 
  d sender recipient amount :=
  if sender =? contract_address then true else
  address_accepts_funds d sender recipient amount.
Close Scope int256.
(* Definition address_accepts_funds_assumption := address_accepts_funds_assumed_for_from_contract. *)
Definition address_accepts_funds_assumption (_ : option ContractState) (_ _ : addr) (_ : wei) := true. (* TODO-Daniel: consider the implications of this or at least write about this assumption. *)
(* The current model also has the implicit assumption that the transfers to a smart contract during a function call via callvalue are always accepted by the contract.
   This could be changed by editing callvalue_prf in the definition of Action, similarly to how it is done for `externalBalanceTransfer` *)



Definition constructor_call_context :=
  {| origin := Int256.zero;
     caller := Int256.zero;
     callvalue := 0;
     coinbase := Int256.zero;
     chainid := Int256.zero |}.

Definition constructor_blockchain_state :=
  {| timestamp := snapshot_timestamp;
    block_number := snapshot_number;
    balance := snapshot_balances;
    blockhash := snapshot_blockhash;
    contract_state := init_global_abstract_data |}.

Program Definition constructor_machine_env := make_machine_env contract_address constructor_blockchain_state constructor_call_context address_accepts_funds_assumption _ _ _.
Next Obligation.
unfold Int256.modulus, two_power_nat. lia.
Defined.
Next Obligation.
unfold noOverflowOrUnderflowInTransfer.
rewrite Z.add_0_r. rewrite Z.sub_0_r.
(* Search "&&" true. *)
rewrite andb_true_iff.
split.
pose proof (snapshot_balances_valid_prf Int256.zero). lia.
pose proof (snapshot_balances_valid_prf contract_address). lia.
Defined.

Context {HmemOps: MemoryModelOps mem}.
Context {memModelOps : MemoryModelOps mem}.

Transparent ERC20WrappedEth_constructor_opt.
Definition init_state :=
  match runStateT (ERC20WrappedEth_constructor_opt constructor_machine_env) init_global_abstract_data
  with
  | Some (_, d) => Some d
  | None => None
  end.

(* The following lemma is true for the current setup right now, but would not be true in general, e.g. if the constructor allowed arbitrary setting of a storage variable. *)
Lemma same_init : init_state = Some init_global_abstract_data.
Proof.
  unfold init_state.
  unfold ERC20WrappedEth_constructor_opt.
  simpl.
  unfold init_global_abstract_data.
  reflexivity.
Qed.

(** TODO: tweak the above to be more true to the actual deployment of a contract on the EVM and integrate into the below. Also consider whether other aspects of BlockchainState should be affected, in particular balances - especially since it seems contracts can have ether transferred to them on deployment. *)

(* end hide *)

(** * Initial State *)

(** Similarly to the crowdfunding smart contract, the initial state is automatically provided by the DeepSEA system. The initial smart contract data given by [init_global_abstract_data] includes the three variables of the contract, as well as the initially empty [Outgoing_transfer_recipient_and_amount] entry. Here is the contents of the initial smart contract state: *)

(* begin hide *)
(* begin snippet print_init_global_abstract_data_wrappedEth *)
Print init_global_abstract_data. (* .all *)
(* end snippet print_init_global_abstract_data_wrappedEth *)
(* end hide *)
(** %\inputsnippets{ERC20WrappedEth_Alectryonified/print_init_global_abstract_data_wrappedEth}%*)

(* begin hide *)
Definition initial_state :=
  mkBlockchainState
    snapshot_timestamp
    snapshot_number
    snapshot_balances
    snapshot_blockhash
    init_global_abstract_data (* TODO, check if init_global_abstract_data is the right way to get initial contract data. *)
.

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

Definition update_balances sender recipient amount balances : (addr -> wei) :=
  (* Here the balances are updated without checking for overflows. Overflow checks must be done elsewhere. *)
  fun a => 
  if (sender =? recipient)%int256 then balances a else
    if (a =? sender)%int256 then (balances sender) - amount else
     if (a =? recipient)%int256 then (balances recipient) + amount
      else balances a.

Definition update_balance before latest_balances : BlockchainState :=
  mkBlockchainState
  (timestamp before)
  (block_number before)
  latest_balances
  (blockhash before)
  (contract_state before)
.


(* TODO-Review - This defines how balances are updated in the model after transferEth *)
Definition current_balances 
  (* Note on where insufficient balance-checking takes place:
     Overflow and underflow of balances must already have been checked before this function.
     (i.e. before a transfer is placed in Outgoing_transfer_recipient_and_amount it should
           have been checked to ensure no overflow/underflow.)
     Currently this check is expected to be implemented by the me_transfer definition.
     !! Ensure you are using an appropriate me_transfer definition. !! *)
  (successful_transfer : option (addr * Z))
  (initial_balances : addr -> wei) 
  : (addr -> wei) :=
    match successful_transfer with
      | None => initial_balances
      | Some (recipient, amount) => 
          update_balances contract_address recipient amount initial_balances
    end.

Definition new_balance_after_contract_call (before : BlockchainState) (context : CallContext) (d : ContractState) : (addr -> wei) :=
    (current_balances
      (Outgoing_transfer_recipient_and_amount d)
      (update_balances (caller context) contract_address (callvalue context) (balance before))).

Definition resetTransfers (d : ContractState) : ContractState :=
  {|
  Outgoing_transfer_recipient_and_amount := None;
  ERC20WrappedEth_wrapped := ERC20WrappedEth_wrapped d;
  ERC20WrappedEth_allowances := ERC20WrappedEth_allowances d;
  ERC20WrappedEth__totalSupply := ERC20WrappedEth__totalSupply d
  |}.

Definition next_blockchain_state (before : BlockchainState) (context : CallContext) (d : ContractState) : BlockchainState :=
  mkBlockchainState
    (timestamp before)
    (block_number before)
    (new_balance_after_contract_call before context d)
    (blockhash before)
    (resetTransfers d).

Definition next_blockchain_state_keep_transfer (before : BlockchainState) (context : CallContext) (d : ContractState) : BlockchainState :=
  mkBlockchainState
    (timestamp before)
    (block_number before)
    (new_balance_after_contract_call before context d)
    (blockhash before)
    d.
(* end hide *)

(** * Step Function *)

(** The step function is similar to the step function for the crowdfunding smart contract, with the transitions for the smart contract functions replaced by the functions for the ERC-20 wrapped ether smart contract. %\Cref{fig:state-machine-diagram-ERC20WrappedEth}% summarises the possible actions described by the [Action] dependent type and the [step] function for the ERC-20 wrapped ether smart contract. [Action] and [step] are included in %\Cref{app:ERC20WrappedEth-action,app:ERC20WrappedEth-step}%. *)

(**%
\begin{figure}[H]
  \caption{Outline of the step function for the ERC-20 wrapped ether smart contract}
  \label{fig:state-machine-diagram-ERC20WrappedEth}
  \centering
\includegraphics[width=0.75\textwidth]{state-machine-diagram-ERC20WrappedEth}
\end{figure}
%*)

(** * Reachability Predicate *)

(** The reachability predicate is identical to the crowdfunding smart contract reachability predicate described in %\Cref{sec:reachability-predicate}%, except that the definition for the step function now is the version for the ERC-20 wrapped ether smart contract. *)

(* begin hide *)
Inductive Action (before : BlockchainState) :=
  | call_ERC20WrappedEth_totalSupply (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_totalSupply_prf : 
          runStateT (ERC20WrappedEth_totalSupply_opt
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | call_ERC20WrappedEth_balanceOf (_owner : addr) (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_balanceOf_prf : 
          runStateT (ERC20WrappedEth_balanceOf_opt _owner
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | call_ERC20WrappedEth_transfer (_to : addr) (_value : wei) (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_transfer_prf : 
          runStateT (ERC20WrappedEth_transfer_opt _to _value
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | call_ERC20WrappedEth_transferFrom (_from _to : addr) (_value : wei) (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_transferFrom_prf : 
          runStateT (ERC20WrappedEth_transferFrom_opt _from _to _value
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | call_ERC20WrappedEth_allowance (_owner _spender : addr) (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_allowance_prf : 
          runStateT (ERC20WrappedEth_allowance_opt _owner _spender
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | call_ERC20WrappedEth_approve (_spender : addr) (_value : wei) (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_approve_prf : 
          runStateT (ERC20WrappedEth_approve_opt _spender _value
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | call_ERC20WrappedEth_approveSafely (_spender : addr) (_currentValue _value : wei) (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_approveSafely_prf : 
          runStateT (ERC20WrappedEth_approveSafely_opt _spender _currentValue _value
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
| call_ERC20WrappedEth_mint (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_mint_prf : 
          runStateT (ERC20WrappedEth_mint_opt
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | call_ERC20WrappedEth_burn (_value : wei) (context : CallContext)
      (callvalue_bounded_prf : 0 <= callvalue context < Int256.modulus)
      (balances_bounded_prf : forall a, 0 <= (balance before) a < Int256.modulus)
      (callvalue_prf : noOverflowOrUnderflowInTransfer (caller context)
        contract_address (callvalue context) (balance before) = true)
      r (* The return value *)
      contract_state_after (* The contract state afterwards *)
      (case_burn_prf : 
          runStateT (ERC20WrappedEth_burn_opt _value
                      (make_machine_env contract_address before context
                        address_accepts_funds_assumption callvalue_bounded_prf
                          balances_bounded_prf callvalue_prf))
                    (contract_state before)
          = Some (r, contract_state_after))
  | externalBalanceTransfer (sender recipient : addr) (amount : wei)
      (prf : sender <> contract_address /\ amount >= 0 /\
        ((noOverflowOrUnderflowInTransfer sender recipient amount (balance before))
        && (address_accepts_funds_assumption None sender recipient amount) = true))
  | timePassing (block_count time_passing : int256)
      (prf : validTimeChange block_count time_passing (block_number before)
              (timestamp before) = true)
  | revert.

Definition step
  (before : BlockchainState) (action : Action before) : BlockchainState :=
match action with
| call_ERC20WrappedEth_totalSupply context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_balanceOf _owner context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_balanceOf_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_transfer _to _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_transfer_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_transferFrom _from _to _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_transferFrom_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_allowance _owner _spender context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_approve _spender _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_approve_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_approveSafely _spender _currentValue _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_approveSafely_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_mint context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state before context d_after
| call_ERC20WrappedEth_burn _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state before context d_after
| timePassing block_count time_passing prf => 
    updateTimeAndBlock before block_count time_passing
| externalBalanceTransfer sender recipient amount prf =>
    update_balance before (update_balances sender recipient amount (balance before))
| revert => before
end.

Definition step_keep_transfer
  (before : BlockchainState) (action : Action before) : BlockchainState :=
match action with
| call_ERC20WrappedEth_totalSupply context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_balanceOf _owner context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_balanceOf_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_transfer _to _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_transfer_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_transferFrom _from _to _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_transferFrom_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_allowance _owner _spender context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_approve _spender _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_approve_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_approveSafely _spender _currentValue _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_approveSafely_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_mint context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state_keep_transfer before context d_after
| call_ERC20WrappedEth_burn _value context
    callvalue_bounded_prf balances_bounded_prf callvalue_prf
    r d_after case_donate_prf => 
      next_blockchain_state_keep_transfer before context d_after
| timePassing block_count time_passing prf => 
    updateTimeAndBlock before block_count time_passing
| externalBalanceTransfer sender recipient amount prf =>
    update_balance before (update_balances sender recipient amount (balance before))
| revert => before
end.

Record Step := mkStep
  {
    Step_state : BlockchainState;
    Step_action : Action Step_state
  }.

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

Inductive ReachableFromBy from : BlockchainState -> Step -> list Step -> Prop :=
| initial_case (Hno_leftover_outgoings : Outgoing_transfer_recipient_and_amount (contract_state from) = None)
      (next_action : Action from)
    : ReachableFromBy from from (mkStep from next_action) [mkStep from next_action]
| step_case (prevSt : BlockchainState) (prev : Step) (prevList : list Step)
            (Hprev : ReachableFromBy from prevSt prev prevList)
    (next_action : Action (stepOnce prev))
    : ReachableFromBy from  (stepOnce prev) 
     (stepOnceAndWrap prev next_action)
     (stepOnceAndWrap prev next_action :: prevList)  .
(* begin snippet ReachableFromByLinkStateToStep *)
Lemma ReachableFromByLinkStateToStep : forall st st' s l,
  ReachableFromBy st st' s l -> st' = Step_state s.
Proof.
  intros. (* .all -.h#snapshot_balances_valid_prf *)
  destruct H; reflexivity.
Qed.
(* end snippet ReachableFromByLinkStateToStep *)     

Lemma ReachableFromByLinkStepToList : forall st st' s l,
  ReachableFromBy st st' s l -> exists tl, s :: tl = l.
Proof.
  intros.
  destruct H.
  - exists []. reflexivity.
  - exists prevList. reflexivity.
Qed.

Ltac reachableFromByLinks := 
  match goal with
  | H : ReachableFromBy _ _ _ _ |- _ => 
    let StateToStepName := fresh "HReachableFromByLinkStateToStep" in
    let StepToListName := fresh "HReachableFromByLinkStepToList" in
    epose proof (ReachableFromByLinkStateToStep _ _ _ _ H) as StateToStepName;
    epose proof (ReachableFromByLinkStepToList _ _ _ _ H) as StepToListName
  end.

(* TODO: Add to some note or Wiki so I don't forget this lemma *)
Lemma NoLeftoverOutgoings : forall {st st' s l},
  ReachableFromBy st st' s l -> Outgoing_transfer_recipient_and_amount (contract_state st') = None.
Proof.
  intros.
  induction H.
  - assumption.
  - unfold stepOnce.
    unfold step.
    destruct (Step_action prev) eqn:Case; simpl; try reflexivity.
    all: reachableFromByLinks; subst; assumption.
Qed.

(* Ugh *)
(* Inductive ReachableFromBy from (s : BlockchainState) (next_action : Action s) : list Step -> Prop :=
| initial_case (first_action : Action from)
    : ReachableFromBy from from first_action [mkStep from first_action]
| step_case (prevList : list Step) (Hprev : ReachableFromBy from s next_action prevList)
    (next_step_action : Action (step s next_action))
    : ReachableFromBy from (step s next_action) next_step_action
     (stepOnce s next_action next_step_action :: prevList)  
. *)

(* Definition ReachableFrom from state := exists l step', ReachableFromBy from state step' l.

Definition Reachable := ReachableFrom initial_state. *)

Ltac Hlinks := 
  match goal with
  | H : ReachableFromBy _ _ _ _ |- _ => 
    let StateToStepName := fresh "HS" in
    let StepToListName := fresh "HL" in
    epose proof (ReachableFromByLinkStateToStep _ _ _ _ H) as StateToStepName;
    epose proof (ReachableFromByLinkStepToList _ _ _ _ H) as StepToListName
  end.

Ltac destruct_and :=
  match goal with
    | [ H : (_ /\ _) |- _ ] => destruct H
  end.

Definition since_as_long (P : BlockchainState -> Prop) (Q : BlockchainState -> Prop) (R : Step -> Prop) : Prop :=
  forall (steps : list Step) (from_state to_state : BlockchainState) (to_step : Step),
    ReachableFromBy from_state to_state to_step steps ->
    P from_state ->
    (forall sa, List.In sa steps -> R sa) ->
    Q to_state.

Notation "Q `since` P `as-long-as` R" := (since_as_long P Q R) (at level 1).
  
(* Definition unwrappable a amount state :=
  (forall a : addr, 0 <= balance state a < Int256.modulus) ->
  exists (action : Action state),
          Outgoing_transfer_recipient_and_amount (contract_state (step_keep_transfer state action)) = Some (a, amount)
          /\
          (* The following represents the idea that the action must not merely be some action by anyone, but it must be one do-able by the caller. And that the caller can get their funds back without giving away more funds, hence the callvalue must be zero. *)
          match action with
          | call_WrappedEth_wrap context _ _ _ _ _ _ => callvalue context = 0 /\ caller context = a
          | call_WrappedEth_unwrap context _ _ _ _ _ _ => callvalue context = 0 /\ caller context = a
          | call_WrappedEth_transfer _ context _ _ _ _ _ _ => callvalue context = 0 /\ caller context = a
          | _ => False
          end. *)

(* Definition amount_in_bounds a state :=
  (0 <=? (get_default 0 a (WrappedEth_wrapped (contract_state state)))) = true
  /\ ((get_default 0 a (WrappedEth_wrapped (contract_state state))) <? Int256.modulus) = true.

Lemma amount_stays_in_bounds :
  forall a from_state to_state to_step steps,
  ReachableFromBy from_state to_state to_step steps ->
  amount_in_bounds a from_state
  -> amount_in_bounds a to_state.
Proof.
intros.
induction H.
- assumption.
- destruct next_action.   
  + Transparent WrappedEth_wrap_opt.
    unfold WrappedEth_wrap_opt in case_donate_prf.
    ds_inv. subst. simpl in *.
    unfold amount_in_bounds.
Admitted.
    rewrite Z.eqb_eq in H13. rewrite H13. *)

(* end hide *)

(** * Preservation of Wrapped Ether Record Theorem *)

(** Having defined the ERC-20 wrapped ether smart contract, we now explore the proofs of four theorems about it, looking at two in fine detail. First, the [wrapped_preserved] theorem. This is similar to the [donation_preserved] theorem and also makes use of the same [since_as_long] predicate. We define the properties [wrappedAtLeast] and [no_transfer_or_burn_from] which are similar to the properties [donation_recorded] and [no_claims_from], respectively.

%
The reason we use the property \emph{wrappedAtLeast}, that at least a specified amount is wrapped rather than that exactly a specific amount being wrapped, is because the user may be the recipient of transfers which increase their balance beyond the amount they initially have wrapped. We are aiming to prove that once at least a specified amount is wrapped then at least that amount remains wrapped, unless there is a call to any of the \coq{transfer}, \coq{transferFrom} or \coq{burn} functions.
%
*)

(** %\Needspace{\coqbaselineskiptwo}% *)
Definition wrappedAtLeast (a : addr) (amount : Z) (s : BlockchainState) :=
    Int256Tree.get_default 0 a (ERC20WrappedEth_wrapped (contract_state s)) >= amount /\ amount > 0.

(** %\Needspace{\coqbaselineskipsix}% *)
Definition no_transfer_or_burn_from (a : addr) (s : Step) :=
  match Step_action s with
  | (call_ERC20WrappedEth_burn _ context _ _ _ _ _ _) => caller context <> a
  | (call_ERC20WrappedEth_transferFrom _from _ _ context _ _ _ _ _ _) => _from <> a
  | (call_ERC20WrappedEth_transfer _ _ context _ _ _ _ _ _) => caller context <> a
  | _ => True
  end.

(**
The proof has aspects which are similar to the [donation_preserved] theorem. However, one difference is that the definitions of the ERC-20 wrapped ether smart contract functions (defined in %\Cref{sec:contract-source-code-erc20-wrapped-ether}%) make use of assertions instead of a heavy use of `if' statements as in the crowdfunding smart contract. Since the DeepSEA system places assertions directly as hypotheses this results in less explicit case analysis in this proof, as is clear by the slightly shallower nesting of bullets.

Now we unpack the proof of the %\coq{wrapped_preserved}% theorem.
*)

(* Alectryon: wrapped_preserved *)
Theorem wrapped_preserved (a : addr) (amount : Z) :
               (wrappedAtLeast a amount)
  `since`      (wrappedAtLeast a amount)
  `as-long-as` (no_transfer_or_burn_from a).
Proof. (* .in *)
(** *)
unfold since_as_long. intros. (* .out -.h#* .h#H *)
(** We proceed by induction on the reachability predicate [H]. *)
induction H.
- (* .out -.h#* .h#H0 *)
  (** We prove the base case using the assumption from property [P] in the [since_as_long] predicate. *)
  assumption.
- (** Proving the inductive case requires case analysis on the action, breaking our goal into twelve subgoals corresponding to the twelve transitions shown in %\Cref{fig:state-machine-diagram-ERC20WrappedEth}%. 

The first nine subgoals correspond to the functions of the smart contract and the final three correspond to the generic actions of time passing on the blockchain, ether transfers not originating from the contract, and the catch-all revert action for failure cases. First there is some housekeeping. *)
  assert(wrappedAtLeast a amount prevSt) as IHReachableFromByCorollary by
    (apply IHReachableFromBy; intros; apply H1; apply in_cons; assumption).
  unfold wrappedAtLeast in *;
    destruct IHReachableFromByCorollary 
      as [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
  split; [|assumption].
  Hlinks.
  assert(no_transfer_or_burn_from a prev) by
    (apply H1; destruct HL; subst; right; left; auto).
  destruct prev; autounfold in *; simpl in *.
  unfold no_transfer_or_burn_from in H2.
  destruct Step_action0; simpl in *.

(** The first subgoal is the case for the %\coq{totalSupply}% function, which does not alter the %\coq{wrapped}% mapping. As a result, the goal follows from a corollary of the inductive hypothesis after establishing that the %\coq{wrapped}% mapping is not altered. The proof engages with the definition of the %\coq{totalSupply}% function after unfolding it and makes use of the [ds_inv] tactic. *)
  + Transparent ERC20WrappedEth_totalSupply_opt.
    unfold ERC20WrappedEth_totalSupply_opt in case_totalSupply_prf.
    ds_inv; subst; simpl in *. (* .out -.h#* .h#case_totalSupply_prf *)
(** We use inversion to establish that [contract_state_after = contract_state Step_state0] *)
    inversion case_totalSupply_prf. (* .out -.h#* .h#IHReachableFromByCorollary1 *)
(** Now the goal matches a corollary of the inductive hypothesis exactly. *)
    exact IHReachableFromByCorollary1.
(** Next is the case for the %\coq{balanceOf}% function, which also does not alter the %\coq{wrapped}% mapping. The proof is essentially identical to that for the %\coq{totalSupply}% case. *)
  + Transparent ERC20WrappedEth_balanceOf_opt.
    unfold ERC20WrappedEth_balanceOf_opt in case_balanceOf_prf.
    ds_inv; subst; simpl in *.
    inversion case_balanceOf_prf.
    exact IHReachableFromByCorollary1.
(** We then have the %\coq{transfer}% function. Here, we need to consider whether or not the recipient, [_to], is the address we are considering, [a]. *)
  + Transparent ERC20WrappedEth_transfer_opt.
    unfold ERC20WrappedEth_transfer_opt in case_transfer_prf.
    clear H HL.
    ds_inv; subst; simpl in *.
    destruct (a =? _to)%int256 eqn:Case.
      * apply Int256eq_true in Case. (* .out -.h#* .h#Case *)
(** In the case where it is, the %\coq{wrapped}% funds for [a] increase, or stay the same if the transfer is of value 0, so the property [wrappedAtLeast] is preserved. *)
        subst.
        apply (f_equal negb) in H12. rewrite negb_involutive in H12.
        apply Int256eq_false in H12. (* .out -.h#* .h#H12 *)
        rewrite get_default_so by auto. (* .out -.h#* *)
        apply geb_ge in H4.
        rewrite get_default_ss. (* .out -.h#* .h#IHReachableFromByCorollary1 .h#H4 *)
        clear -IHReachableFromByCorollary1 H4. (* .none *)
(** Now the goal follows from the inductive hypothesis, along with the knowledge that the argument %\coq{_value}% is non-negative. This should always be the case but needs to be guaranteed by an assertion due to the current handling of unsigned integers in DeepSEA. The goal is solvable by the linear integer arithmetic tactic. *)
        lia.
(** In the case where the recipient [_to] is not the address [a] that we are concerned with then the alterations this function makes to the %\coq{wrapped}% mapping do not affect the address [a] so our goal is exactly a corollary of the inductive hypothesis after rewriting the goal. *)
      * apply Int256eq_false in Case. (* .out -.h#* .h#H2 *)
(** Here, we use the ``get default set other'' lemma, along with the hypotheses shown to simplify the goal because the key we are retrieving the value for is not the one that is having its value changed. The statement of [get_default_so] is shown below. *)
        Check get_default_so. (* .in .unfold .no-hyps .no-goals .messages *)
        rewrite get_default_so by auto. (* .out -.h#* .h#Case *)
        rewrite get_default_so by auto.  (* .out -.h#* .h#IHReachableFromByCorollary1 *)
        exact IHReachableFromByCorollary1.
(** Next, we have the %\coq{transferFrom}% function. The proof is identical to the case for %\coq{transfer}% once the definition of %\coq{transferFrom}% has been unfolded. *)
  + Transparent ERC20WrappedEth_transferFrom_opt.
    unfold ERC20WrappedEth_transferFrom_opt in case_transferFrom_prf.
    clear H HL.
    ds_inv; subst; simpl in *.
    destruct (a =? _to)%int256 eqn:Case.
    * apply Int256eq_true in Case.
      subst.
      apply (f_equal negb) in H12. rewrite negb_involutive in H12.
      apply Int256eq_false in H12.
      rewrite get_default_so by auto.
      apply geb_ge in H4.
      rewrite get_default_ss.
      clear -IHReachableFromByCorollary1 H4.
      lia.
    * apply Int256eq_false in Case.
      rewrite get_default_so by auto.
      rewrite get_default_so by auto.
      exact IHReachableFromByCorollary1.
(** Next is the %\coq{allowance}% function. It does not alter the %\coq{wrapped}% mapping. The proof is essentially identical to the proofs for the other cases which do not alter the %\coq{wrapped}% mapping. *)
  + Transparent ERC20WrappedEth_allowance_opt.
    unfold ERC20WrappedEth_allowance_opt in case_allowance_prf.
    ds_inv; subst; simpl in *.
    inversion case_allowance_prf.
    exact IHReachableFromByCorollary1.
(** The %\coq{approve}% function also does not alter the %\coq{wrapped}% mapping and the proof is similar to such previous cases. *)
  + Transparent ERC20WrappedEth_approve_opt.
    unfold ERC20WrappedEth_approve_opt in case_approve_prf.
    ds_inv; subst; simpl in *.
    inversion case_approve_prf.
    clear H HL case_approve_prf.
    destruct (_value >=? 0); simpl in *; inversion H4.
    simpl in *.
    exact IHReachableFromByCorollary1.
(** The %\coq{approveSafely}% function needs to have an explicit case analysis in the proof due to its `if' statement. But it also does not alter the %\coq{wrapped}% mapping and the proof bears strong similarities to previous cases. *)
  + Transparent ERC20WrappedEth_approveSafely_opt.
    unfold ERC20WrappedEth_approveSafely_opt in case_approveSafely_prf.
    ds_inv; subst; simpl in *.
    inversion case_approveSafely_prf. (* .out -.h#* *)
    clear H HL case_approveSafely_prf.
    destruct (_value >=? 0); simpl in *; inversion H4.
(** Here we need to perform case analysis on the guard of the `if' statement to demonstrate that neither case affects the %\coq{wrapped}% mapping. *)
    destruct (_currentValue =?
                get_default 0 _spender
                  (get_default (empty Z) (caller context)
                    (ERC20WrappedEth_allowances (contract_state Step_state0))));
      inversion H3; simpl in *; exact IHReachableFromByCorollary1.
(** We now move on to the two functions which are added beyond the ERC-20 specification and make this a %\emph{wrapped ether}% ERC-20 token. Firstly, the %\coq{mint}% function. *)
  + Transparent ERC20WrappedEth_mint_opt.
    unfold ERC20WrappedEth_mint_opt in case_mint_prf.
    clear H HL. simpl in *.
    ds_inv; subst; simpl in *.
    destruct(caller context =? contract_address)%int256; simpl in *;
    ds_inv; subst; simpl in *; try discriminate.
    destruct(callvalue context >? 0)%int256; simpl in *; simpl in *;
    ds_inv; subst; simpl in *; try discriminate.
    inversion case_mint_prf; simpl in *.
(** The heart of this branch of the proof is where we consider whether or not the address we are concerned with, [a], is the caller. We perform case analysis. *)
    destruct (a =? (caller context))%int256 eqn:Case.
    * apply Int256eq_true in Case. (* .out -.h#* .h#Case *)
(** First we consider when the address [a] is the caller. *)
      rewrite <- Case in *.
      rewrite get_default_ss. (* .out -.h#* .h#IHReachableFromByCorollary1 .h#callvalue_bounded_prf *)
      clear -IHReachableFromByCorollary1 callvalue_bounded_prf. (* .none *)
(** Having simplified the goal, it now follows from the inductive hypothesis plus the knowledge that the callvalue is non-negative. The goal is solved by the linear integer arithmetic tactic. *)
      lia.
(** In the case where the address [a] is not the caller, the goal simplifies to a corollary of the inductive hypothesis. This is because the setting of values in the %\coq{wrapped}% mapping does not affect the value read for the address [a]. *)
    * apply Int256eq_false in Case. (* .out -.h#* .h#Case *)
      rewrite get_default_so by apply Case. (* .out -.h#* .h#IHReachableFromByCorollary1 *)
      exact IHReachableFromByCorollary1.
(** The next transition is for the [burn] smart contract function. As with all these proofs, the body of the function is engaged with, along with use of the [ds_inv] to make inferences from the knowledge that the body of the function succeeds.

We have assumed from the [no_transfer_or_burn_from] property in [since_as_long] that the caller is not the address, [a], which we are interested in. As a result, the proof of this case follows from simplifying the goal using our assumption. This case should not be provable without the [no_transfer_or_burn_from] assumption. *)
  + Transparent ERC20WrappedEth_burn_opt.
    unfold ERC20WrappedEth_burn_opt in case_burn_prf.
    clear H HL.
    ds_inv; subst.
    * simpl in *. (* .out -.h#* .h#H2 *)
(** At this point in the proof we have assumed from the [no_transfer_or_burn_from] property in [since_as_long] that the caller is not the address, [a], which we are interested in. As a result we can use the [get_default_so] lemma to effectively ignore the [set] which is affecting an address other than [a].

We dismiss the antecedent of [get_default_so] by the tactic [auto] which swaps the order of [a] and [caller context] in [H2] and applies it. *)
      rewrite get_default_so by auto. (* .out -.h#* *)
      exact IHReachableFromByCorollary1.
(** This case corresponds to the transfer of ether to the user failing. Since we have assumed via the success-calls approach that the contract succeeds, this case leads to a contradictory assumption [Heqb] and can be dismissed via the principle of ex falso quodlibet. *)
    * exfalso. simpl in *. apply Int256eq_true in Heqb. (* .out -.h#* .h#Heqb *)
      inversion Heqb.
(** The final three cases correspond to the external balance transfer, time passing and revert cases. Since none of these actions alter the %\coq{wrapped}% mapping, they are trivially true by a corollary of the inductive hypothesis. *)
  + rewrite <- HS. apply IHReachableFromByCorollary1.
  + rewrite <- HS. apply IHReachableFromByCorollary1.
  + rewrite <- HS. apply IHReachableFromByCorollary1.
(** *)
Qed.
(* Alectryon-end *)

(* begin hide *)
Opaque ERC20WrappedEth_totalSupply_opt.
Opaque ERC20WrappedEth_balanceOf_opt.
Opaque ERC20WrappedEth_transfer_opt.
Opaque ERC20WrappedEth_transferFrom_opt.
Opaque ERC20WrappedEth_approve_opt.
Opaque ERC20WrappedEth_approveSafely_opt.
Opaque ERC20WrappedEth_allowance_opt.
Opaque ERC20WrappedEth_mint_opt.
Opaque ERC20WrappedEth_burn_opt.
(* end hide *)

(** * Transfer Correctness Theorem *)

(** This theorem demonstrates how one can phrase a theorem without referring to the blockchain model introduced in %\Cref{sec:Modelling}%. Here we universally quantify over a number of variables, and then assume that these variables result in a successful call to the %\coq{transfer}% function. It is also possible to demonstrate that a function succeeds, rather than assuming it does, which gives a theorem more similar to the [can_claim_back] theorem from %\Cref{sec:can-claim-back-crowdfunding}%.

Once we have assumed the %\coq{transfer}% function succeeds, we assume that the variables [_from_balance_before], [_to_balance_before], [_from_balance_after], and [_to_balance_after] have their natural meanings with respect to the %\coq{wrapped}% mapping in the %\emph{contract\_state before}% and [contract_state_after]. Then we aim to prove that the amounts stored are altered as expected for a transfer of value in the resulting [contract_state_after]. In other words, we aim to prove that if the smart contract function succeeds, then the %\coq{wrapped}% mapping successfully reflects this transfer. By assuming that the smart contract succeeds, we have implicitly assumed that the sender, [_from], has a sufficient balance to make the transfer. This is due to assuming that the %\coq{transfer}% function succeeds, which implies the sender had a sufficient balance. 

Here is the proof of the theorem. *)

(* Alectryon: transfer_correct *)
Theorem transfer_correct :
  forall _to _value _from_balance_before _from_balance_after
                    _to_balance_before   _to_balance_after
   before context r contract_state_after
    callvalue_bounded_prf balances_bounded_prf callvalue_prf,
  runStateT (ERC20WrappedEth_transfer_opt _to _value
    (make_machine_env contract_address before context
      address_accepts_funds_assumption callvalue_bounded_prf
      balances_bounded_prf callvalue_prf))
    (contract_state before)
= Some (r, contract_state_after)
  -> _from_balance_before = 
      Int256Tree.get_default 0 (caller context)
        (ERC20WrappedEth_wrapped (contract_state before))
  -> _to_balance_before = 
      Int256Tree.get_default 0 _to
        (ERC20WrappedEth_wrapped (contract_state before))
  -> _from_balance_after = 
      Int256Tree.get_default 0 (caller context)
        (ERC20WrappedEth_wrapped contract_state_after)
  -> _to_balance_after = 
      Int256Tree.get_default 0 _to
        (ERC20WrappedEth_wrapped contract_state_after)
  ->     _to_balance_after = _to_balance_before + _value
     /\  _from_balance_after = _from_balance_before - _value.
Proof. (* .in *)
(** Here, we proceed by introducing the variables and hypotheses, unfolding the definition of the %\coq{transfer}% function, and using the tactic [ds_inv] to make use of the knowledge that the %\coq{transfer}% function succeeds. *)
intros.
Transparent ERC20WrappedEth_transfer_opt. unfold ERC20WrappedEth_transfer_opt in H.
ds_inv. subst. simpl in *. (* .out -.h#* *)
(** This leaves us with two subgoals joined by a conjunction, which have had [WrappedEth_wrapped contract_state_after] replaced with the value determined by [ds_inv] as what must be equal with that. The changes correspond to the effect on the %\coq{wrapped}% mapping from the two lines preceding the %\coq{emit}% statement of the %\coq{transfer}% function shown in %\Cref{list:ERC20WrappedEth-code-7}%. *)
split.
(** The first goal corresponds to [_to_balance_after = _to_balance_before + _value]. *)
  - apply (f_equal negb) in H9. rewrite negb_involutive in H9.
    apply Int256eq_false in H9. (* .out -.h#* .h#H9 *)
(** The first conjunct is solved by application of the tactics [get_default_so] and [get_default_ss]. First, [get_default_so] eliminates the setting of the [_from] balance in the chain of updates shown in the goal. This is a correct simplification because transfers to oneself are not permitted by this smart contract. *)
    rewrite get_default_so by auto. (* .out -.h#* *)
(** The goal now can be simplified further because we are reading the value for the same key which was just set, for the recipient [_to]. *)
    rewrite get_default_ss. (* .out -.h#* *)
(** Now we have shown that the first conjunct simplifies to the value we expected and the goal can be solved via the [reflexivity] tactic. *)
    reflexivity.
(** The second goal corresponds to [_from_balance_after = _from_balance_before - _value]. *)
  - apply negb_true_iff in H9. apply Int256eq_false in H9. (* .out -.h#* .h#H9 *)
  (** Here, the intermediate step of setting the value for the recipient in the mapping does not affect the value of getting the value for the caller from the mapping which is set afterwards. As a result, we can rewrite using the [get_default_ss] lemma. *)
    
    rewrite get_default_ss. (* .out -.h#* *)
    (** Now the goal has been simplified to the expected form and is trivially solvable by the [reflexivity] tactic. *)
    reflexivity.
(** *)
Qed.
(* Alectryon-end *)

(* begin hide *)
Opaque ERC20WrappedEth_transfer_opt.
(* end hide *)

(** * Correctness of the Total Supply Variable Theorem *)

(** %\label{sec:total_supply_correct}% *)

(** The %\coq{totalSupply}% variable is intended to track the total amount of wrapped ether recorded in the %\coq{wrapped}% mapping. The goal here is to prove that at all reachable states, this is indeed the case. 
We use the same [Safe] predicate as for the crowdfunding smart contract.
*)

(** %\Needspace{\coqbaselineskiptwo}% *)
Definition Safe P :=
  forall state s l, ReachableFromBy initial_state state s l -> P state.

(** The property, [total_supply_tracks_correctly], declares that the %\coq{totalSupply}% variable equals the sum of the values in the %\coq{wrapped}% mapping. We also require the property that all values in the wrapped mapping are non-negative as a sanity check required due to the way unsigned integers are handled in DeepSEA. *)

(** %\Needspace{\coqbaselineskipsix}% *)
Definition total_supply_tracks_correctly state :=
  sum (ERC20WrappedEth_wrapped (contract_state state))
    = (ERC20WrappedEth__totalSupply (contract_state state))
    /\ (forall key value, get_default 0 key
    (ERC20WrappedEth_wrapped (contract_state state)) 
       = value -> (value >= 0)).

(** Now we are ready to prove the theorem. Below is an outline of the proof. The full proof is available in %\Cref{app:ERC20WrappedEth-total-supply-correct}%. *)

(* Alectryon: total_supply_correct *)
Theorem total_supply_correct : Safe total_supply_tracks_correctly.
Proof. (* .in *)
(** *)
unfold Safe. intros. (* .out -.h#* .h#H *)
(** We proceed by induction on the reachability predicate [H]. *)
induction H.
- (** We prove the base case by unfolding the initial state and simplifying. *)
  unfold total_supply_tracks_correctly.
  unfold initial_state. simpl.
  split.
  * unfold sum. unfold empty. unfold Int256Tree.fold1. simpl.
    reflexivity.
  * intros. unfold get_default in H. rewrite gempty in H.
    lia.
- (** We then perform case analysis on the twelve possible transitions shown in %\Cref{fig:state-machine-diagram-ERC20WrappedEth}%. *)
  Hlinks.
  destruct prev; autounfold in *; simpl in *.
  destruct Step_action0; simpl in *.
(** This is the case for %\coq{totalSupply}%, which does not alter the %\coq{wrapped}% mapping or %\coq{totalSupply}% variable. *)
  + Transparent ERC20WrappedEth_totalSupply_opt.
    unfold ERC20WrappedEth_totalSupply_opt in case_totalSupply_prf.
    ds_inv; subst; simpl in *.
    inversion case_totalSupply_prf.
    unfold total_supply_tracks_correctly.
    simpl.
    unfold total_supply_tracks_correctly in IHReachableFromBy.
    split.
    * apply IHReachableFromBy.
    * destruct IHReachableFromBy as
        [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
      apply IHReachableFromByCorollary2.
(** This is the case for %\coq{balanceOf}%, which does not alter the wrapped mapping. The proof is identical to the previous case and is omitted for brevity. *)
  + Transparent ERC20WrappedEth_balanceOf_opt.
    abbreviated.
    unfold ERC20WrappedEth_balanceOf_opt in case_balanceOf_prf. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    inversion case_balanceOf_prf. (* .none *)
    unfold total_supply_tracks_correctly. (* .none *)
    simpl. (* .none *)
    unfold total_supply_tracks_correctly in IHReachableFromBy. (* .none *)
    split. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2]. (* .none *)
      apply IHReachableFromByCorollary2. (* .none *)
(** We then have the %\coq{transfer}% function. Here, we will show the heart of the proof. The remainder of the proof is available in %\Cref{app:ERC20WrappedEth-total-supply-correct}%. *)
  + Transparent ERC20WrappedEth_transfer_opt.
    unfold ERC20WrappedEth_transfer_opt in case_transfer_prf. (* .none *)
    destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2]. (* .none *)
    clear H HL. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    * (* .none *) unfold total_supply_tracks_correctly. (* .none *)
      simpl. (* .none *)
      unfold total_supply_tracks_correctly in IHReachableFromByCorollary1. (* .none *)
      rewrite <- IHReachableFromByCorollary1. (* .none *)
      apply (f_equal negb) in H9. (* .none *)
      rewrite negb_involutive in H9. (* .none *) simpl in H9. (* .none *)
      apply Int256eq_false in H9. (* .none *)
      split. (* .none *)
      -- (* .out -.h#* *)
         (** The heart of this proof is the application of the [constant_sum'] lemma, which shows the following: *)
         Check Int256Tree_Properties.constant_sum'. (* .in .unfold .no-hyps .no-goals .messages *)
         (** A careful examination of the goal will show that this lemma is appropriate for this situation. *)
         apply Int256Tree_Properties.constant_sum'; try reflexivity. (* .out -.h#* .h#H9 *)
         (** After dismissing most of the requirements of [constant_sum'] with the [reflexivity] tactic, we dismiss the final assumption based on [H9] which comes from the requirement that you cannot transfer to yourself. *)
         assumption.
      -- (* .none *)
         intros. (* .none *)
         apply (f_equal negb) in H5. (* .none *) rewrite negb_involutive in H5. (* .none *)
         apply Int256eq_false in H5. (* .none *)
         destruct((caller context) =? key)%int256 eqn:SCase. (* .none *)
           ++ (* .none *) apply Int256eq_true in SCase. (* .none *) subst. (* .none *)
              rewrite get_default_ss. (* .none *)
              lia. (* .none *)
           ++ (* .none *) apply Int256eq_false in SCase. (* .none *) subst. (* .none *)
              rewrite get_default_so by auto. (* .none *)
              pose proof (IHReachableFromByCorollary2 (key) (get_default 0 (key)
                   (ERC20WrappedEth_wrapped (contract_state Step_state0)))). (* .none *)
              destruct(_to =? key)%int256 eqn:SSCase. (* .none *)
                ** (* .none *) apply Int256eq_true in SSCase. (* .none *) subst. (* .none *)
                   rewrite get_default_ss. (* .none *)
                   lia. (* .none *)
                ** (* .none *) apply Int256eq_false in SSCase. (* .none *) subst. (* .none *)
                   rewrite get_default_so by auto. (* .none *)
                   lia. (* .none *)
(** The %\coq{transferFrom}% case is identical to %\coq{transfer}% case except that instead of [(caller context)] we have [_from]. The proof is omitted for brevity and is available in %\Cref{app:ERC20WrappedEth-total-supply-correct}%. *)
  + Transparent ERC20WrappedEth_transferFrom_opt.
    abbreviated.
    unfold ERC20WrappedEth_transferFrom_opt in case_transferFrom_prf. (* .none *)
    destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2]. (* .none *)
    clear H HL. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    * (* .none *) unfold total_supply_tracks_correctly. (* .none *)
      simpl. (* .none *)
      unfold total_supply_tracks_correctly in IHReachableFromByCorollary1. (* .none *)
      rewrite <- IHReachableFromByCorollary1. (* .none *)
      apply (f_equal negb) in H9. (* .none *)
      rewrite negb_involutive in H9. (* .none *) simpl in H9. (* .none *)
      apply Int256eq_false in H9. (* .none *)
      split. (* .none *)
      -- (* .none *)
         Check Int256Tree_Properties.constant_sum'.  (* .none *)
         apply Int256Tree_Properties.constant_sum'; try reflexivity. (* .none *)
         assumption. (* .none *)
      -- (* .none *)
         intros. (* .none *)
         apply (f_equal negb) in H5. (* .none *) rewrite negb_involutive in H5. (* .none *)
         apply Int256eq_false in H5. (* .none *)
         destruct(_from =? key)%int256 eqn:SCase. (* .none *)
           ++ (* .none *) apply Int256eq_true in SCase. (* .none *) subst. (* .none *)
              rewrite get_default_ss. (* .none *)
              lia. (* .none *)
           ++ (* .none *) apply Int256eq_false in SCase. (* .none *) subst. (* .none *)
              rewrite get_default_so by auto. (* .none *)
              pose proof (IHReachableFromByCorollary2 (key) (get_default 0 (key)
                   (ERC20WrappedEth_wrapped (contract_state Step_state0)))). (* .none *)
              destruct(_to =? key)%int256 eqn:SSCase. (* .none *)
                ** (* .none *) apply Int256eq_true in SSCase. (* .none *) subst. (* .none *)
                   rewrite get_default_ss. (* .none *)
                   lia. (* .none *)
                ** (* .none *) apply Int256eq_false in SSCase. (* .none *) subst. (* .none *)
                   rewrite get_default_so by auto. (* .none *)
                   lia. (* .none *)
(** As with the %\coq{balanceOf}% and %\coq{totalSupply}% functions, the case for the %\coq{allowance}% function does not alter any fields relevant to this lemma and its proof (omitted here) is identical to the proofs for those functions. *)
  + Transparent ERC20WrappedEth_allowance_opt.
    abbreviated.
    unfold ERC20WrappedEth_allowance_opt in case_allowance_prf. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    inversion case_allowance_prf. (* .none *)
    unfold total_supply_tracks_correctly. (* .none *)
    simpl. (* .none *)
    unfold total_supply_tracks_correctly in IHReachableFromBy. (* .none *)
    split. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2]. (* .none *)
      apply IHReachableFromByCorollary2. (* .none *)
(** The proofs for %\coq{approve}% and %\coq{approveSafely}% are very similar to previous cases because they also do not alter variables relevant to this theorem. *)
  + Transparent ERC20WrappedEth_approve_opt.
    abbreviated.
    unfold ERC20WrappedEth_approve_opt in case_approve_prf. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    inversion case_approve_prf. (* .none *)
    clear H HL case_approve_prf. (* .none *)
    destruct (_value >=? 0); simpl in *; inversion H1. (* .none *)
    unfold total_supply_tracks_correctly. (* .none *)
    simpl. (* .none *)
    apply IHReachableFromBy. (* .none *)
  + Transparent ERC20WrappedEth_approveSafely_opt.
    abbreviated.
    unfold ERC20WrappedEth_approveSafely_opt in case_approveSafely_prf. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    inversion case_approveSafely_prf. (* .none *) 
    clear H HL case_approveSafely_prf. (* .none *)
    destruct (_value >=? 0); simpl in *; [|inversion H1]. (* .none *)
    destruct (_currentValue =?
                get_default 0 _spender
                  (get_default (empty Z) (caller context)
                    (ERC20WrappedEth_allowances (contract_state Step_state0)))); simpl in *. (* .none *)
    inversion H1. (* .none *)
    unfold total_supply_tracks_correctly. (* .none *) simpl. (* .none *) assumption. (* .none *)
    inversion H1. (* .none *)
    assumption. (* .none *)
(** Now for the %\coq{mint}% and %\coq{burn}% functions, which do alter the %\coq{totalSupply}% variable. These functions are central to whether this theorem holds or not.
The heart of this case is the update to the %\coq{totalSupply}% variable. This part of the proof is shown below, the remainder is available in %\Cref{app:ERC20WrappedEth-total-supply-correct}%. *)
    + Transparent ERC20WrappedEth_mint_opt.
    unfold ERC20WrappedEth_mint_opt in case_mint_prf. (* .none *)
    clear H HL. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    * (* .none *) unfold total_supply_tracks_correctly. (* .none *)
      simpl. (* .none *)
      destruct IHReachableFromBy as
        [IHReachableFromByCorollary1 IHReachableFromByCorollary2]. (* .none *)
      unfold total_supply_tracks_correctly in IHReachableFromByCorollary1. (* .none *)
      split. (* .none *)
      -- unfold sum. (* .out -.h#* *)
        (** Here we can see that [sum] is defined as a kind of [fold] using the function [Z.add] over the mapping with an initial value of zero. *)
        Print sum. (* .in .unfold .no-hyps .no-goals .messages *)
        (** Now consider the lemma [sum_set_x_minus_from_arbitrary_init], discussed as a part of the proof themes in %\Cref{chap:ProofThemes}%. *)
        Check sum_set_x_minus_from_arbitrary_init. (* .in .unfold .no-hyps .no-goals .messages *)

        (** When summing a list, if we replace one element, [v], with another, the sum of the list is now equal to the original sum plus the new element and minus the replaced element, [v]. 
        This is essentially the heart of this proof, except that here the new element equals the old element, [v], plus the value of the callvalue. So the resulting sum is the original sum plus [v] plus the callvalue minus [v]. This simplifies to just the original sum plus the callvalue.
        
        Also, we are not dealing with a list but rather the values of the Coq representation of the DeepSEA %\coq{mapping}% type. Nevertheless, the idea of the proof remains the same at a high level. *)
        
        rewrite sum_set_x_minus_from_arbitrary_init with
          (v:=(get_default 0 (caller context)
            (ERC20WrappedEth_wrapped
               (contract_state Step_state0)))) by reflexivity. (* .out -.h#* *)
(** This is clearer if we save the value of the caller's entry in the wrapped mapping from beforehand as [v] and fold the occurrences of [sum]. *)
        remember((get_default 0 (caller context)
          (ERC20WrappedEth_wrapped
            (contract_state Step_state0)))) as v.
        fold (sum (ERC20WrappedEth_wrapped (contract_state Step_state0))). (* .out -.h#* *)
(** Now we can see that the left-hand side corresponds to a more useful form equal to the sum of the wrapped mapping after the callvalue is added to the entry for the caller in the mapping. *)
        rewrite <- IHReachableFromByCorollary1.  (* .out -.h#* *)
(** After rewriting the %\coq{totalSupply}% variable's value based on the inductive hypothesis, it is clear that the left and right hand sides evaluate to the same value. We can show this using the linear integer arithmetic tactic. *)
        lia.
(** The other branch of the proof, showing that all values in the %\coq{wrapped}% mapping are nonnegative, follows from proof techniques that have been demonstrated already in this thesis and is omitted for brevity. It is available in %\Cref{app:ERC20WrappedEth-total-supply-correct}%. *)
      -- abbreviated.
         intros. (* .none *)
          subst. (* .none *)
          pose proof (IHReachableFromByCorollary2 (caller context) (get_default 0 (caller context)
              (ERC20WrappedEth_wrapped (contract_state Step_state0)))). (* .none *)
          destruct((caller context) =? key)%int256 eqn:SCase. (* .none *)
            ++ (* .none *) apply Int256eq_true in SCase. (* .none *) subst. (* .none *)
              rewrite get_default_ss. (* .none *)
              lia. (* .none *)
            ++ (* .none *) apply Int256eq_false in SCase. (* .none *) subst. (* .none *)
              rewrite get_default_so by auto. (* .none *)
              pose proof (IHReachableFromByCorollary2 key (get_default 0 key
              (ERC20WrappedEth_wrapped (contract_state Step_state0)))). (* .none *)
              lia. (* .none *)
    + Transparent ERC20WrappedEth_burn_opt.
    unfold ERC20WrappedEth_burn_opt in case_burn_prf. (* .none *)
    clear H HL. (* .none *)
    ds_inv; subst; simpl in *. (* .none *)
    * (* .none *) unfold total_supply_tracks_correctly. (* .none *)
      simpl. (* .none *)
      destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2]. (* .none *)
      unfold total_supply_tracks_correctly in IHReachableFromByCorollary1. (* .none *)
      split. (* .none *)
      -- (* .none *) unfold sum. (* .none *)
        rewrite sum_set_x_minus_from_arbitrary_init with
          (v:=(get_default 0 (caller context)
            (ERC20WrappedEth_wrapped
               (contract_state Step_state0)))) by reflexivity. (* .none *)
        remember((get_default 0 (caller context)
          (ERC20WrappedEth_wrapped
            (contract_state Step_state0)))) as v. (* .none *)
        fold (sum (ERC20WrappedEth_wrapped (contract_state Step_state0))). (* .none *)
        rewrite <- IHReachableFromByCorollary1. (* .no-in .unfold -.h#* *)
        lia.
        -- (* .none *) intros. (* .none *)
        subst. (* .none *)
        pose proof (IHReachableFromByCorollary2 (caller context) (get_default 0 (caller context)
            (ERC20WrappedEth_wrapped (contract_state Step_state0)))). (* .none *)
        destruct((caller context) =? key)%int256 eqn:SCase. (* .none *)
          ++ (* .none *) apply Int256eq_true in SCase. (* .none *) subst. (* .none *)
            rewrite get_default_ss. (* .none *)
            lia. (* .none *)
          ++ (* .none *) apply Int256eq_false in SCase. (* .none *) subst. (* .none *)
            rewrite get_default_so by auto. (* .none *)
            pose proof (IHReachableFromByCorollary2 key (get_default 0 key
            (ERC20WrappedEth_wrapped (contract_state Step_state0)))). (* .none *)
            lia. (* .none *)
    * (* .none *) inversion Heqb. (* .none *)
(** The final three proof-goals correspond to the actions for time passing, a balance transfer not originating from the contract, and the revert case. Since none of these actions affect the %\coq{wrapped}% mapping, they all follow from the inductive hypothesis. *)
  + rewrite <- HS. unfold total_supply_tracks_correctly.
      simpl. apply IHReachableFromBy.
  + rewrite <- HS. unfold total_supply_tracks_correctly.
      simpl. apply IHReachableFromBy.
  + rewrite <- HS. unfold total_supply_tracks_correctly.
      simpl. apply IHReachableFromBy.
(** *)
Qed.
(* Alectryon-end *)

(** As a corollary to the above theorem, we can now easily show that, as a sanity check, in all reachable states the %\coq{wrapped}% mapping holds only nonnegative values. First we define the property we are trying to show is a safety property. *)

(** %\Needspace{\coqbaselineskipfour}% *)
Definition balances_positive state :=
  (forall key value, get_default 0 key
               (ERC20WrappedEth_wrapped (contract_state state)) 
                  = value -> (value >= 0)).

(* Alectryon: balances_always_positive *)
Theorem balances_always_positive : Safe balances_positive.
Proof. (* .in *)
(** *)
unfold Safe.
intros.
pose proof (total_supply_correct state s l H). (* .out -.h#* .h#H0 *)
unfold balances_positive, total_supply_tracks_correctly in *.
destruct H0 as [H0 H1]. (* .out -.h#* .h#H0 .h#H1 *)
(** Here, we have extracted the evidence of the property [balances_positive] from the previous theorem [total_supply_correct]. We can also see the other conjunct from that theorem as [H0]. *)
assumption.
(** *)
Qed.
(* Alectryon-end *)

(* begin hide *)
Opaque ERC20WrappedEth_totalSupply_opt.
Opaque ERC20WrappedEth_balanceOf_opt.
Opaque ERC20WrappedEth_transfer_opt.
Opaque ERC20WrappedEth_transferFrom_opt.
Opaque ERC20WrappedEth_approve_opt.
Opaque ERC20WrappedEth_approveSafely_opt.
Opaque ERC20WrappedEth_allowance_opt.
Opaque ERC20WrappedEth_mint_opt.
Opaque ERC20WrappedEth_burn_opt.
(* end hide *)

(** * Sufficient Funds Safe Theorem *)

(** Finally, we will discuss a theorem analogous to the [sufficient_funds_safe] theorem for the crowdfunding smart contract. This time, the proof builds upon the [total_supply_correct] theorem, so we will be able to avoid reasoning directly about the Coq representation of the DeepSEA %\coq{mapping}% type.

Here is the invariant we aim to prove as a safety property. Having proved the [balances_always_positive] theorem, we omit that condition for our proof goal here. *)

(** %\Needspace{\coqbaselineskipthree}% *)
Definition balance_backed state :=
  sum (ERC20WrappedEth_wrapped (contract_state state))
      <= (balance state contract_address).

(** Now we aim to prove that [balance_backed] is a safety property for the ERC-20 wrapped ether smart contract. A proof of this theorem gives us confidence that the smart contract always has a sufficient balance to refund every user. It eliminates the possibility that someone has written a back-door to siphon away funds. However, this theorem alone does not prevent funds from being forever locked in the contract. To prove such a property requires a theorem similar to the [can_claim_back] theorem shown for the crowdfunding smart contract in %\Cref{sec:can-claim-back-crowdfunding}%. 

Here, we will focus only on the heart of the proof. The full proof is available in %\Cref{app:ERC20WrappedEth-sufficient-funds-safe}%. *)

(* Alectryon: erc20_sufficient_funds_safe *)
Theorem sufficient_funds_safe : Safe balance_backed.
Proof. (* .in *)
(** *)
unfold Safe. (* .none *) intros. (* .none *)
pose proof (total_supply_correct state s l H). (* .none *)
unfold total_supply_tracks_correctly in H0. (* .none *)
unfold balance_backed. (* .none *)
destruct H0. (* .none *)
rewrite H0. (* .none *)
clear H0 H1. (* .none *)
induction H.
- simpl. (* .out -.h#* .h#snapshot_balances_valid_prf *)
  (** In the base case, we rely upon the assumption made that the snapshot balances are in a valid range as a part of a snapshot approach described in %\Cref{sec:snapshot}%. *)
  apply snapshot_balances_valid_prf.
- abbreviated.
  Hlinks. (* .none *)
  destruct prev; autounfold in *; simpl in *. (* .none *)
  destruct Step_action0; simpl in *. (* .none *)
  + Transparent ERC20WrappedEth_totalSupply_opt.
    abbreviated.
    unfold ERC20WrappedEth_totalSupply_opt in case_totalSupply_prf. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    inversion case_totalSupply_prf. (* .none *)
    unfold new_balance_after_contract_call. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    rewrite H0. (* .none *)
    unfold current_balances, update_balances. (* .none *)
    rewrite Int256.eq_true. (* .none *)
    destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) rewrite Int256.eq_sym. (* .none *)
      rewrite Case. (* .none *)
      lia. (* .none *)
  + Transparent ERC20WrappedEth_balanceOf_opt.
    abbreviated.
    unfold ERC20WrappedEth_balanceOf_opt in case_balanceOf_prf. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    inversion case_balanceOf_prf. (* .none *)
    unfold new_balance_after_contract_call. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    rewrite H0. (* .none *)
    unfold current_balances, update_balances. (* .none *)
    rewrite Int256.eq_true. (* .none *)
    destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) rewrite Int256.eq_sym. (* .none *)
      rewrite Case. (* .none *)
      lia. (* .none *)
  + Transparent ERC20WrappedEth_transfer_opt.
    abbreviated.
    unfold ERC20WrappedEth_transfer_opt in case_transfer_prf. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    clear HL H. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    unfold new_balance_after_contract_call. (* .none *)
    simpl. (* .none *)
    rewrite H0. (* .none *)
    unfold current_balances, update_balances. (* .none *)
    rewrite Int256.eq_true. (* .none *)
    destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) rewrite Int256.eq_sym. (* .none *)
      rewrite Case. (* .none *)
      lia. (* .none *)
  + Transparent ERC20WrappedEth_transferFrom_opt.
    abbreviated.
    unfold ERC20WrappedEth_transferFrom_opt in case_transferFrom_prf. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    clear HL H. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    unfold new_balance_after_contract_call. (* .none *)
    simpl. (* .none *)
    rewrite H0. (* .none *)
    unfold current_balances, update_balances. (* .none *)
    rewrite Int256.eq_true. (* .none *)
    destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) rewrite Int256.eq_sym. (* .none *)
      rewrite Case. (* .none *)
      lia. (* .none *)
  + Transparent ERC20WrappedEth_allowance_opt.
    abbreviated.
    unfold ERC20WrappedEth_allowance_opt in case_allowance_prf. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    clear HL H. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    unfold new_balance_after_contract_call. (* .none *)
    simpl. (* .none *)
    rewrite H0. (* .none *)
    unfold current_balances, update_balances. (* .none *)
    rewrite Int256.eq_true. (* .none *)
    destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) rewrite Int256.eq_sym. (* .none *)
      rewrite Case. (* .none *)
      lia. (* .none *)
  + Transparent ERC20WrappedEth_approve_opt.
    abbreviated.
    unfold ERC20WrappedEth_approve_opt in case_approve_prf. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    clear HL H. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    unfold new_balance_after_contract_call. (* .none *)
    simpl. (* .none *)
    rewrite H0. (* .none *)
    unfold current_balances, update_balances. (* .none *)
    rewrite Int256.eq_true. (* .none *)
    destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
    * (* .none *) apply IHReachableFromBy. (* .none *)
    * (* .none *) rewrite Int256.eq_sym. (* .none *)
      rewrite Case. (* .none *)
      lia. (* .none *)
  + Transparent ERC20WrappedEth_approveSafely_opt.
    abbreviated.
    unfold ERC20WrappedEth_approveSafely_opt in case_approveSafely_prf. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    clear HL H. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    * (* .none *) unfold new_balance_after_contract_call. (* .none *)
      simpl. (* .none *)
      rewrite H0. (* .none *)
      unfold current_balances, update_balances. (* .none *)
      rewrite Int256.eq_true. (* .none *)
      destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
      -- (* .none *) apply IHReachableFromBy. (* .none *)
      -- (* .none *) rewrite Int256.eq_sym. (* .none *)
        rewrite Case. (* .none *)
        lia. (* .none *)
    * (* .none *) unfold new_balance_after_contract_call. (* .none *) simpl. (* .none *) rewrite H0. (* .none *)
      unfold current_balances, update_balances. (* .none *)
      rewrite Int256.eq_true. (* .none *)
      destruct((caller context) =? contract_address)%int256 eqn:Case. (* .none *)
      -- (* .none *) apply IHReachableFromBy. (* .none *)
      -- (* .none *) rewrite Int256.eq_sym. (* .none *)
         rewrite Case. (* .none *)
         lia. (* .none *)
  + Transparent ERC20WrappedEth_mint_opt.
    abbreviated.
    unfold ERC20WrappedEth_mint_opt in case_mint_prf. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    clear HL H. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    unfold new_balance_after_contract_call. (* .none *)
    simpl. (* .none *)
    rewrite H0. (* .none *)
    unfold current_balances, update_balances. (* .none *)
    rewrite Int256.eq_true. (* .none *)
    apply (f_equal negb) in H2. (* .none *) rewrite negb_involutive in H2. (* .none *)
    simpl in H2. (* .none *)
    rewrite H2. (* .none *)
    rewrite Int256.eq_sym in H2. (* .none *)
    rewrite Z.gtb_lt in H6. (* .none *)
    rewrite H2. (* .out -.h#* .h#IHReachableFromBy .h#H6 *)
    clear -IHReachableFromBy. (* .none *)
    (** Here we see that in the successful case of minting a wrapped ether token, the inequality increases on both sides by the callvalue. As a result the [balance_backed] property is maintained. *)
    lia.
  + Transparent ERC20WrappedEth_burn_opt.
    abbreviated.
    unfold ERC20WrappedEth_burn_opt in case_burn_prf. (* .none *)
    pose proof (NoLeftoverOutgoings H). (* .none *)
    clear HL H. (* .none *)
    ds_inv; subst; simpl in *. (* .none *) 
    * (* .none *) 
      unfold new_balance_after_contract_call. (* .none *)
      simpl. (* .none *)
      unfold current_balances, update_balances. (* .none *)
      rewrite Int256.eq_true. (* .none *)
      apply (f_equal negb) in H6. (* .none *) rewrite negb_involutive in H6. (* .none *)
      simpl in H6. (* .none *)
      rewrite H6. (* .none *)
      rewrite Int256.eq_sym in H6. (* .none *)
      rewrite Z.geb_le in H2. (* .none *)
      rewrite Z.eqb_eq in H10. (* .none *) rewrite H10. (* .none *)
      rewrite Z.add_0_r, Z.sub_0_r. (* .none *)
      rewrite Z.geb_le in H16. (* .none *)
      rewrite H6. (* .out -.h#* .h#IHReachableFromBy .h#H2 *)
      clear -IHReachableFromBy H2. (* .none *)
      (** For the %\coq{burn}% case, this time the inequality is reduced on the left and right by the argument %\coq{_value}% and so the property is maintained. *)
      lia.
    * exfalso. (* .out -.h#* .h#Heqb *)
    (** We also have the scenario where the transfer fails, which we assume not to be the case as part of the successful-calls approach discussed in %\Cref{sec:successful-calls}%. This case is dismissed by the [inversion] tactic and the contradictory knowledge that the %\coq{transferEth}% function returned a zero when it was assumed to return a one in order for the function to succeed.
    The aim of this theorem is to show that in all reachable states, the [balance_backed] property is maintained. It would be a separate proof goal to show that a user can successfully withdraw funds and the proof would be similar to the [can_claim_back] theorem discussed for the crowdfunding smart contract in %\Cref{sec:can-claim-back-crowdfunding}%. *)
    inversion Heqb.
(** Next is the case for external balance transfers, which can only increase the balance, so the property continues to hold. *)
  + unfold current_balances, update_balances.
    abbreviated.
    destruct prf. (* .none *)
    clear H HL. (* .none *)
    apply Int256.eq_false in n. (* .none *)
    rewrite Int256.eq_sym in n. (* .none *)
    rewrite n. (* .none *)
    rewrite HS in *. (* .none *)
    destruct(contract_address =? recipient)%int256 eqn:Case. (* .none *)
    * (* .none *) destruct(sender =? recipient)%int256 eqn:SCase; try lia. (* .none *)
      destruct a. (* .none *)
      apply Int256eq_true in Case. (* .none *)
      rewrite <- Case. (* .out -.h#* .h#IHReachableFromBy .h#H *)
      clear -IHReachableFromBy H. (* .none *)
      (** Here we see the case where some [amount] of ether has been transferred to the smart contract, increasing its balance, but the property is maintained. *)
      lia.
    * (* .none *) destruct(sender =? recipient)%int256 eqn:SCase; try lia. (* .none *)
(** Finally, we have the two cases for time passing and for reverting. Neither affect balances or the %\coq{wrapped}% mapping so they follow from the inductive hypothesis. *)
  + rewrite HS in *. apply IHReachableFromBy.
  + rewrite HS in *. apply IHReachableFromBy.  
(** *)
Qed.
(* Alectryon-end *)

(** * Unsigned Integer Side-Conditions *)
(** %\label{sec:ERC20WrappedEthUnsignedInts}% *)

(** %\input{"../theories/ERC20WrappedEth/proofs/ObjERC20WrappedEthCodeProofs.tex"}% *)

(** * Formal Verification Effort *)
(** The development effort in person-hours for this ERC-20 wrapped ether smart contract with its proofs is shown in %\Cref{tab:effortByTheorem}% and %\Cref{tab:effortSummary}%, in total taking about 24.5 hours. The effort is split into the tasks of implementing, modelling, specifying, proving, and other. Tasks falling into the ``other'' category involved getting familiar with the ERC-20 specification as well as exploratory proof efforts that ended up not being included. For each of the four main theorems as well as for the overflow and underflow safety lemmas, the effort for each is broken down into the time it took to write the specification for the theorem and how long the proof took. The time taken to write the commentary included in this thesis is not included. *)

(** %

\begin{table}[h]
  \caption{Person-hours for specifying and proving the ERC-20 wrapped ether theorems}
  \label{tab:effortByTheorem}
  \centering
  \begin{tabular}{|c|c|c?c|}
       \hline
       \bf Theorem name                 & \bf Specifying  & \bf Proving           & \bf Total             \\
       \thickhline
       \bf \coq{wrapped_preserved}        & 0.8h            & 3.5h                  & 4.3h                   \\
       \hline
       \bf \coq{transfer_correct}         & 0.1h            & 0.4h                  & 0.5h                   \\
       \hline                           
       \bf \coq{total_supply_correct}     & 0.6h            & \multirow{2}{*}{9.3h} &  \multirow{2}{*}{10h}  \\
       \cline{1-2}                        
       \bf \coq{sufficient_funds_safe}    & 0.1h            &                       &                       \\
       \hline
       \bf Overflow/underflow safety  & 1.8h              & 4.6h                    & 6.4h                     \\
       \thickhline
       \bf Total                     & 3.4h            & 17.8h                 & \bf 21.2h              \\
       \hline
  \end{tabular}
\end{table}

\begin{table}[h]
  \caption{Person-hours for all development of the ERC-20 wrapped ether smart contract}
  \label{tab:effortSummary}
  \centering
  \begin{tabular}{|c|c|c|c|c?c|}
       \hline
       \bf Implementing & \bf Modelling & \bf Specifying & \bf Proving & \bf Other & \bf Total  \\
       \thickhline
       1.8h            & 0.2h             & 3.4h           & 17.8h    &    1.3h   & \bf 24.5h        \\
       \hline
  \end{tabular}
\end{table}

% *)

(** While useful as a rough indictator, this information has very limited generality as it is based on the times recorded by myself only. Future work in understanding proof effort and the benefits DeepSEA may provide in this regard, could involve a group of experts being introduced to DeepSEA and then being timed carrying out proofs and writing specifications. A major benefit of the DeepSEA system, in terms of proof effort, is that no effort is spent on bytecode verfication, since DeepSEA's verified compilation removes the need for this. In comparison, 71%% of the proof effort for the verification of the Ethereum 2.0 deposit contract%~\cite{eth2verification}% was spent on bytecode verification. *)

(**

The main Coq file (%\coq{ERC20WrappedEth.v}%) for the ERC-20 wrapped ether smart contract proofs contains 536 lines which relate to specifications and 745 lines which relate to proofs, as counted by the %\coq{coqwc}% utility. In contrast, for the main file for the crowdfunding case study (%\coq{Crowdfunding.v}%) from %\Cref{chap:Crowdfunding}%, there are 399 lines which relate to specification and 733 lines which relate to proofs. These files and those they depend on are available as described in %\Cref{app:Source-Code}%. We also note that the size of the generated bytecode for the crowdfunding smart contract and ERC-20 wrapped ether smart contract are 2511 bytes and 5135 bytes, respectively.

*)

(** * Remarks *)
(** The ERC-20 wrapped ether case study demonstrates that the approach used to verify properties of the crowdfunding smart contract can easily be adapted to other smart contracts, in particular being applied to a realistic ERC-20 token. It also highlights that where there are similarities between smart contracts, such as having a %\coq{backers}%/%\coq{wrapped} mapping, much can be gained from learning how to prove properties about the original smart contract as it is likely that the lemmas required and the structure of the new proofs will resemble the original proofs. This emphasises the point that the more formal proofs are carried out, the easier new proofs will become due to similarities with existing proofs. *)

(* begin hide *)
End Blockchain_Model.

End FunctionalCorrectness.
(* end hide *)












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