:title: ERC-20 Wrapped-ETH Verification in DeepSEA
:css: talk.css
:css: alectryon.css
:css: tango_subtle.css
:js-body: alectryon.js
:slide-numbers: true
:data-transition-duration: 0
:alectryon/serapi/args: -R /home/daniel/Code/Talk-ERC20-DeepSEA-Alectryon/PhD-Thesis-Code-Artefact/DeepSEA DeepSpec -R /home/daniel/Code/Talk-ERC20-DeepSEA-Alectryon/PhD-Thesis-Code-Artefact/Chapter-5-Case-Study-Crowdfunding/Crowdfunding Crowdfunding -R /home/daniel/Code/Talk-ERC20-DeepSEA-Alectryon/PhD-Thesis-Code-Artefact/Chapter-6-Case-Study-ERC-20-Wrapped-Ether-Token/ERC20WrappedEth ERC20WrappedEth -R /home/daniel/Code/Talk-ERC20-DeepSEA-Alectryon/PhD-Thesis-Code-Artefact/Trivial/trivial trivial -R /home/daniel/Code/Talk-ERC20-DeepSEA-Alectryon/PhD-Thesis-Code-Artefact/Chapter-5-Case-Study-Crowdfunding/proofs SmartContract

.. :auto-console: true

----

==========================================
ERC-20 Wrapped-ETH Verification in DeepSEA
==========================================

Dr. Daniel Britten
==================

----

**Overview:**

- Trivial Example in DeepSEA
- ERC-20 Implementation
- Property: Preservation of Wrapped-ETH records
- Property: Transfer Correctness
- Safety Property: Total Supply Variable Tracks
- Safety Property: Sufficient Funds Safe
- Formal Verification Effort

----

**Trivial Example in DeepSEA**

Example: Trivial contract converting `bool` to `int` and keeping track of if it has ever been passed the input `true`

----

.. code:: ocaml

  object signature trivial = {
      const boolToInt : bool -> int;
      boolToIntTracker : bool -> int
  }

  object Trivial : trivial {
      let seenTrueYet : bool := false

      let boolToInt b =
        if b then 1 else 0

      let boolToIntTracker b =
        if b then
          begin
              seenTrueYet := true;
              1
          end
        else 0
  }

  layer CONTRACT = { o = Trivial }

----

.. code:: bash

  $ dsc trivial.ds bytecode
  5b60005b60206109205101610920525b61022660006020610920510301525b60006020
  610920510301516101005260206101002060006020610920510301525b600060006020
  61092051030151555b60206109205103610920525b60005b9050386300000073600039
  386000f35b60006000fd5b610940610920527c01000000000000000000000000000000
  000000000000000000000000006000350480635192f3c01463000000495780631e01e7
  071463000000965760006000fd5b6004355b60006109205101610920525b8063000000
  67576300000085565b600190505b60006109205103610920525b805b90506000526020
  6000f35b60009050630000006c565b60006000fd5b6004355b60206109205101610920
  525b8063000000b4576300000111565b61022660006020610920510301525b60006020
  610920510301516101005260206101002060006020610920510301525b600160006020
  61092051030151555b600190505b60206109205103610920525b805b90506000526020
  6000f35b6000905063000000f8565b60006000fd

----

`$ dsc trivial.ds abi`

.. code:: json

  [ {"type":"constructor",
    "name":"constructor",
    "inputs":[], "outputs":[], "payable":false,
    "constant":false, "stateMutability":"nonpayable"},
  {"type":"function",
    "name":"boolToInt",
    "inputs":[{"name":"b", "type":"bool"}],
    "outputs":[{"name":"", "type":"uint256"}],
    "payable":false,
    "constant":true,
    "stateMutability":"view"},
  {"type":"function",
    "name":"boolToIntTracker",
    "inputs":[{"name":"b", "type":"bool"}],
    "outputs":[{"name":"", "type":"uint256"}],
    "payable":true,
    "constant":false,
    "stateMutability":"payable"}]

----

.. coq:: none

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


`$ dsc trivial.ds coq ...`

.. code:: coq

  if f then ret 1 else ret 0

.. coq:: fold

  Require Import Syntax. (* .none *)
  Print Trivial_boolToInt_opt.
  Print Trivial_boolToInt.

----

`$ dsc trivial.ds coq ...`

.. code:: coq
  
  if f then
    MonadState.modify (update_Trivial_seenTrueYet true) ;;
    ret 1
  else
    ret 0

.. coq:: fold
  
  Print Trivial_boolToIntTracker_opt.
  Print Trivial_boolToIntTracker.

----

.. coq:: fold

  Lemma boolToInt_proof : forall input context before result after HContext1 HContext2 HContext3,
    let machine_environment :=
      (make_machine_env contract_address before context (fun _ _ _ _ => true) HContext1 HContext2 HContext3) in

    runStateT (Trivial_boolToInt_opt input machine_environment) (contract_state before)
      = Some (result, after)
    
    ->
    
    result = 1 <-> input = true.

----

Goal:

.. code:: coq

  result = 1 <-> input = true

.. coq:: fold
  
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

  Print inv_runStateT_branching.
  Print inv_runStateT1_branching.

.. note::

  Remember to click the extra button to show hypotheses for both goals when they are there.

  Note that some hypothesis are hidden in the visualisations for clarity.

  Next next slide has a copy of the contract definition.

----


.. coq:: none

  Lemma boolToInt_proof' : forall input context before result after HContext1 HContext2 HContext3,
      let machine_environment :=
        (make_machine_env contract_address before context (fun _ _ _ _ => true) HContext1 HContext2 HContext3) in

      runStateT (Trivial_boolToInt_opt input machine_environment) (contract_state before)
        = Some (result, after)
      
      ->
      
      result = 1 <-> input = true.

.. coq:: fold

    Proof.
      intros.
      Transparent Trivial_boolToInt_opt. unfold Trivial_boolToInt_opt in H.
      split;
        inv_runStateT_branching; try subst; try discriminate; try reflexivity.
    Qed.

----

.. code:: ocaml

  object signature trivial = {
      const boolToInt : bool -> int;
      boolToIntTracker : bool -> int
  }

  object Trivial : trivial {
      let seenTrueYet : bool := false

      let boolToInt b =
        if b then 1 else 0

      let boolToIntTracker b =
        if b then
          begin
              seenTrueYet := true;
              1
          end
        else 0
  }

  layer CONTRACT = { o = Trivial }

----

.. coq:: none

  End Proof.
  Open Scope nat.

**ERC-20 Wrapped-ETH Implementation**

.. image:: state-machine-diagram-ERC20WrappedEth.png

.. code:: ocaml

  event
      | Transfer (_from : address indexed) (_to : address indexed) (_value : int)
      | Approval (_owner : address indexed) (_spender : address indexed)
                 (_value : int)

  object signature ERC20WrappedEthSig = {
      const totalSupply : unit -> int;
      const balanceOf : address -> int;
      transfer : address * int -> bool;
      transferFrom : address * address * int -> bool;
      const allowance : address * address -> int;
      approve : address * int -> bool;
      approveSafely : address * int * int -> bool;
      mint : unit -> bool;
      burn : int -> bool
  }

  object ERC20WrappedEth () : ERC20WrappedEthSig {
      let wrapped : mapping[address] int := mapping_init
      let allowances : mapping[address] mapping[address] int := mapping_init
      let _totalSupply : int := 0
    

      let totalSupply () =
        _totalSupply
      
      let balanceOf(_owner) = 
        wrapped[_owner]
      
      let transfer(_to, _value) =
        assert(_value >= 0);
        assert(msg_sender <> this_address);
        assert(msg_sender <> _to);
        assert(msg_value = 0);
        let wrapped_amount_from = wrapped[msg_sender] in
        let wrapped_amount_to = wrapped[_to] in
        assert(wrapped_amount_from >= _value);
        wrapped[_to] := wrapped_amount_to + _value;
        wrapped[msg_sender] := wrapped_amount_from - _value;
        emit Transfer(msg_sender, _to, _value);
        true

      let transferFrom(_from, _to, _value) =
        assert(_value >= 0);
        assert(_from <> this_address);
        assert(_from <> _to);
        assert(msg_value = 0);
        let approved_amount = allowances[_from][msg_sender] in
        assert(approved_amount >= _value);
        allowances[_from][msg_sender] := approved_amount - _value;
        let wrapped_amount_from = wrapped[_from] in
        let wrapped_amount_to = wrapped[_to] in
        assert(wrapped_amount_from >= _value);
        wrapped[_to] := wrapped_amount_to + _value;
        wrapped[_from] := wrapped_amount_from - _value;
        emit Transfer(_from, _to, _value);
        true

      let allowance(_owner, _spender) = 
        allowances[_owner][_spender]
      
      let approve (_spender, _value) = 
        assert(_value >= 0);
        allowances[msg_sender][_spender] := _value;
        emit Approval(msg_sender, _spender, _value);
        true

      let approveSafely (_spender, _currentValue, _value) = 
        assert(_value >= 0);
        let actualCurrentValue = allowances[msg_sender][_spender] in
        if (_currentValue = actualCurrentValue) then
          begin
            allowances[msg_sender][_spender] := _value;
            emit Approval(msg_sender, _spender, _value);
            true
          end
        else
          false

      let mint () =
        assert(msg_sender <> this_address);
        assert(msg_value > 0);

        let wrapped_amount = wrapped[msg_sender] in
        wrapped[msg_sender] := wrapped_amount + msg_value;
        let prev_totalSupply = _totalSupply in
        _totalSupply := prev_totalSupply + msg_value;
        emit Transfer(address(0x0), msg_sender, msg_value);
        true
      
      let burn (_value) =
        assert(_value >= 0);
        assert(msg_sender <> this_address);
        assert(msg_value = 0);

        let wrapped_amount = wrapped[msg_sender] in
        assert(wrapped_amount >= _value);
        wrapped[msg_sender] := wrapped_amount - _value;
        let prev_totalSupply = _totalSupply in
        _totalSupply := prev_totalSupply - _value;
        transferEth(msg_sender, _value);
        emit Transfer(msg_sender, address(0x0), _value);
        true
  }

  layer CONTRACT : [ { } ]  {erc20wrappedeth : ERC20WrappedEthSig}  = {
      erc20wrappedeth = ERC20WrappedEth
  }

----

======
Proofs
======

.. image:: whitespace.png

.. image:: whitespace.png

.. coq:: fold

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

  Open Scope Z.
  
  Ltac abbreviated := idtac.
  
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
        simpl.
        rewrite Z.sub_0_r.
        rewrite sum_set_y_remove_from_starting_x.
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

  Section Blockchain_Model.

  Open Scope int256.

  Context
    (snapshot_timestamp : int256)
    (snapshot_number : int256)
    (snapshot_blockhash : int256 -> int256)
    (snapshot_balances : addr -> wei).

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

  Definition address_accepts_funds_assumption (_ : option ContractState) (_ _ : addr) (_ : wei) := true.
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

  (** * Initial State *)

  Print init_global_abstract_data.

  Definition initial_state :=
    mkBlockchainState
      snapshot_timestamp
      snapshot_number
      snapshot_balances
      snapshot_blockhash
      init_global_abstract_data
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

  (** * Step Function *)

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

  Definition stepOnce prev := (step (Step_state prev) (Step_action prev)).
  Definition stepOnceAndWrap prev next_action := (mkStep (stepOnce prev) next_action).
  Hint Unfold stepOnce stepOnceAndWrap.

  (** * Reachability Predicate *)

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
  Lemma ReachableFromByLinkStateToStep : forall st st' s l,
    ReachableFromBy st st' s l -> st' = Step_state s.
  Proof.
    intros. (* snapshot_balances_valid_prf *)
    destruct H; reflexivity.
  Qed.

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


----

**Property: Preservation of Wrapped-ETH records**

.. image:: reachablefromby.svg

.. coq:: in

  Definition since_as_long (P : BlockchainState -> Prop) (Q : BlockchainState -> Prop) (R : Step -> Prop) : Prop :=
    forall (steps : list Step) (from_state to_state : BlockchainState) (to_step : Step),
      ReachableFromBy from_state to_state to_step steps ->
      P from_state ->
      (forall sa, List.In sa steps -> R sa) ->
      Q to_state.

  Notation "Q `since` P `as-long-as` R" := (since_as_long P Q R) (at level 1).
  
  Definition wrappedAtLeast (a : addr) (amount : Z) (s : BlockchainState) :=
      Int256Tree.get_default 0 a (ERC20WrappedEth_wrapped (contract_state s)) >= amount /\ amount > 0.

  Definition no_transfer_or_burn_from (a : addr) (s : Step) :=
    match Step_action s with
    | (call_ERC20WrappedEth_burn _ context _ _ _ _ _ _) => caller context <> a
    | (call_ERC20WrappedEth_transferFrom _from _ _ context _ _ _ _ _ _) => _from <> a
    | (call_ERC20WrappedEth_transfer _ _ context _ _ _ _ _ _) => caller context <> a
    | _ => True
    end.

  Theorem wrapped_preserved (a : addr) (amount : Z) :
                (wrappedAtLeast a amount)
    `since`      (wrappedAtLeast a amount)
    `as-long-as` (no_transfer_or_burn_from a).
  Proof. (* .in *)
  unfold since_as_long. intros. (* .out .unfold -.h#* .h#H *)
  induction H.
  - (* .out .unfold -.h#* .h#H0 *)
      assumption.
  - assert(wrappedAtLeast a amount prevSt) as IHReachableFromByCorollary by
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

    + Transparent ERC20WrappedEth_totalSupply_opt.
      unfold ERC20WrappedEth_totalSupply_opt in case_totalSupply_prf.
      ds_inv; subst; simpl in *. (* .out .unfold -.h#* .h#case_totalSupply_prf *)
      inversion case_totalSupply_prf. (* .out .unfold -.h#* .h#IHReachableFromByCorollary1 *)
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_balanceOf_opt.
      unfold ERC20WrappedEth_balanceOf_opt in case_balanceOf_prf.
      ds_inv; subst; simpl in *.
      inversion case_balanceOf_prf.
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_transfer_opt.
      unfold ERC20WrappedEth_transfer_opt in case_transfer_prf.
      clear H HL.
      ds_inv; subst; simpl in *.
      destruct (a =? _to)%int256 eqn:Case.
        * apply Int256eq_true in Case. (* .out .unfold -.h#* .h#Case *)
          subst.
          apply (f_equal negb) in H12. rewrite negb_involutive in H12.
          apply Int256eq_false in H12. (* .out .unfold -.h#* .h#H12 *)
          rewrite get_default_so by auto. (* .out .unfold -.h#* *)
          apply geb_ge in H4.
          rewrite get_default_ss. (* .out .unfold -.h#* .h#IHReachableFromByCorollary1 .h#H4 *)
          clear -IHReachableFromByCorollary1 H4. (* .none *)
          lia.
        * apply Int256eq_false in Case. (* .out .unfold -.h#* .h#H2 *)
          Check get_default_so. (* .in .unfold .no-hyps .no-goals .messages *)
          rewrite get_default_so by auto. (* .out .unfold -.h#* .h#Case *)
          rewrite get_default_so by auto.  (* .out .unfold -.h#* .h#IHReachableFromByCorollary1 *)
          exact IHReachableFromByCorollary1.
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
    + Transparent ERC20WrappedEth_allowance_opt.
      unfold ERC20WrappedEth_allowance_opt in case_allowance_prf.
      ds_inv; subst; simpl in *.
      inversion case_allowance_prf.
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_approve_opt.
      unfold ERC20WrappedEth_approve_opt in case_approve_prf.
      ds_inv; subst; simpl in *.
      inversion case_approve_prf.
      clear H HL case_approve_prf.
      destruct (_value >=? 0); simpl in *; inversion H4.
      simpl in *.
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_approveSafely_opt.
      unfold ERC20WrappedEth_approveSafely_opt in case_approveSafely_prf.
      ds_inv; subst; simpl in *.
      inversion case_approveSafely_prf. (* .out .unfold -.h#* *)
      clear H HL case_approveSafely_prf.
      destruct (_value >=? 0); simpl in *; inversion H4.
      destruct (_currentValue =?
                  get_default 0 _spender
                    (get_default (empty Z) (caller context)
                      (ERC20WrappedEth_allowances (contract_state Step_state0))));
        inversion H3; simpl in *; exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_mint_opt.
      unfold ERC20WrappedEth_mint_opt in case_mint_prf.
      clear H HL. simpl in *.
      ds_inv; subst; simpl in *.
      destruct(caller context =? contract_address)%int256; simpl in *;
      ds_inv; subst; simpl in *; try discriminate.
      destruct(callvalue context >? 0)%int256; simpl in *; simpl in *;
      ds_inv; subst; simpl in *; try discriminate.
      inversion case_mint_prf; simpl in *.
      destruct (a =? (caller context))%int256 eqn:Case.
      * apply Int256eq_true in Case. (* .out .unfold -.h#* .h#Case *)
        rewrite <- Case in *.
        rewrite get_default_ss. (* .out .unfold -.h#* .h#IHReachableFromByCorollary1 .h#callvalue_bounded_prf *)
        clear -IHReachableFromByCorollary1 callvalue_bounded_prf. (* .none *)
        lia.
      * apply Int256eq_false in Case. (* .out .unfold -.h#* .h#Case *)
        rewrite get_default_so by apply Case. (* .out .unfold -.h#* .h#IHReachableFromByCorollary1 *)
        exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_burn_opt.
      unfold ERC20WrappedEth_burn_opt in case_burn_prf.
      clear H HL.
      ds_inv; subst.
      * simpl in *. (* .out .unfold -.h#* .h#H2 *)
        rewrite get_default_so by auto. (* .out .unfold -.h#* *)
        exact IHReachableFromByCorollary1.
      * exfalso. simpl in *. apply Int256eq_true in Heqb. (* .out .unfold -.h#* .h#Heqb *)
        inversion Heqb.
    + rewrite <- HS. apply IHReachableFromByCorollary1.
    + rewrite <- HS. apply IHReachableFromByCorollary1.
    + rewrite <- HS. apply IHReachableFromByCorollary1.
  Qed.

.. coq:: none
  
  Opaque ERC20WrappedEth_totalSupply_opt.
  Opaque ERC20WrappedEth_balanceOf_opt.
  Opaque ERC20WrappedEth_transfer_opt.
  Opaque ERC20WrappedEth_transferFrom_opt.
  Opaque ERC20WrappedEth_approve_opt.
  Opaque ERC20WrappedEth_approveSafely_opt.
  Opaque ERC20WrappedEth_allowance_opt.
  Opaque ERC20WrappedEth_mint_opt.
  Opaque ERC20WrappedEth_burn_opt.

**Full proof**

.. coq:: fold

  Theorem wrapped_preserved' (a : addr) (amount : Z) :
                (wrappedAtLeast a amount)
    `since`      (wrappedAtLeast a amount)
    `as-long-as` (no_transfer_or_burn_from a).
  Proof.
  unfold since_as_long. intros. (* H *)
  induction H.
  - (* H0 *)
    assumption.
  - assert(wrappedAtLeast a amount prevSt) as IHReachableFromByCorollary by
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
    + Transparent ERC20WrappedEth_totalSupply_opt.
      unfold ERC20WrappedEth_totalSupply_opt in case_totalSupply_prf.
      ds_inv; subst; simpl in *. (* case_totalSupply_prf *)
      inversion case_totalSupply_prf. (* IHReachableFromByCorollary1 *)
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_balanceOf_opt.
      unfold ERC20WrappedEth_balanceOf_opt in case_balanceOf_prf.
      ds_inv; subst; simpl in *.
      inversion case_balanceOf_prf.
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_transfer_opt.
      unfold ERC20WrappedEth_transfer_opt in case_transfer_prf.
      clear H HL.
      ds_inv; subst; simpl in *.
      destruct (a =? _to)%int256 eqn:Case.
        * apply Int256eq_true in Case. (* Case *)
          subst.
          apply (f_equal negb) in H12. rewrite negb_involutive in H12.
          apply Int256eq_false in H12. (* H12 *)
          rewrite get_default_so by auto.
          apply geb_ge in H4.
          rewrite get_default_ss. (* IHReachableFromByCorollary1 H4 *)
          clear -IHReachableFromByCorollary1 H4.
          lia.
        * apply Int256eq_false in Case. (* H2 *)
          Check get_default_so.
          rewrite get_default_so by auto. (* Case *)
          rewrite get_default_so by auto.  (* IHReachableFromByCorollary1 *)
          exact IHReachableFromByCorollary1.
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
    + Transparent ERC20WrappedEth_allowance_opt.
      unfold ERC20WrappedEth_allowance_opt in case_allowance_prf.
      ds_inv; subst; simpl in *.
      inversion case_allowance_prf.
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_approve_opt.
      unfold ERC20WrappedEth_approve_opt in case_approve_prf.
      ds_inv; subst; simpl in *.
      inversion case_approve_prf.
      clear H HL case_approve_prf.
      destruct (_value >=? 0); simpl in *; inversion H4.
      simpl in *.
      exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_approveSafely_opt.
      unfold ERC20WrappedEth_approveSafely_opt in case_approveSafely_prf.
      ds_inv; subst; simpl in *.
      inversion case_approveSafely_prf.
      clear H HL case_approveSafely_prf.
      destruct (_value >=? 0); simpl in *; inversion H4.
      destruct (_currentValue =?
                  get_default 0 _spender
                    (get_default (empty Z) (caller context)
                      (ERC20WrappedEth_allowances (contract_state Step_state0))));
        inversion H3; simpl in *; exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_mint_opt.
      unfold ERC20WrappedEth_mint_opt in case_mint_prf.
      clear H HL. simpl in *.
      ds_inv; subst; simpl in *.
      destruct(caller context =? contract_address)%int256; simpl in *;
      ds_inv; subst; simpl in *; try discriminate.
      destruct(callvalue context >? 0)%int256; simpl in *; simpl in *;
      ds_inv; subst; simpl in *; try discriminate.
      inversion case_mint_prf; simpl in *.
      destruct (a =? (caller context))%int256 eqn:Case.
      * apply Int256eq_true in Case. (* Case *)
        rewrite <- Case in *.
        rewrite get_default_ss. (* IHReachableFromByCorollary1 callvalue_bounded_prf *)
        clear -IHReachableFromByCorollary1 callvalue_bounded_prf.
        lia.
      * apply Int256eq_false in Case. (* Case *)
        rewrite get_default_so by apply Case. (* IHReachableFromByCorollary1 *)
        exact IHReachableFromByCorollary1.
    + Transparent ERC20WrappedEth_burn_opt.
      unfold ERC20WrappedEth_burn_opt in case_burn_prf.
      clear H HL.
      ds_inv; subst.
      * simpl in *. (* H2 *)
        rewrite get_default_so by auto.
        exact IHReachableFromByCorollary1.
      * exfalso. simpl in *. apply Int256eq_true in Heqb. (* Heqb *)
        inversion Heqb.
    + rewrite <- HS. apply IHReachableFromByCorollary1.
    + rewrite <- HS. apply IHReachableFromByCorollary1.
    + rewrite <- HS. apply IHReachableFromByCorollary1.
  Qed.

.. coq:: none

  Opaque ERC20WrappedEth_totalSupply_opt.
  Opaque ERC20WrappedEth_balanceOf_opt.
  Opaque ERC20WrappedEth_transfer_opt.
  Opaque ERC20WrappedEth_transferFrom_opt.
  Opaque ERC20WrappedEth_approve_opt.
  Opaque ERC20WrappedEth_approveSafely_opt.
  Opaque ERC20WrappedEth_allowance_opt.
  Opaque ERC20WrappedEth_mint_opt.
  Opaque ERC20WrappedEth_burn_opt.

----

**Property: Transfer Correctness**

.. coq:: fold

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
  Proof.
  intros.
  Transparent ERC20WrappedEth_transfer_opt. unfold ERC20WrappedEth_transfer_opt in H.
  ds_inv. subst. simpl in *.
  split.
    - apply (f_equal negb) in H9. rewrite negb_involutive in H9.
      apply Int256eq_false in H9. (* H9 *)
      rewrite get_default_so by auto.
      rewrite get_default_ss.
      reflexivity.
    - apply negb_true_iff in H9. apply Int256eq_false in H9. (* H9 *)
      rewrite get_default_ss.
      reflexivity.
  Qed.

.. coq:: none

  Opaque ERC20WrappedEth_transfer_opt.

----

**Safety Property: Total Supply Variable Tracks**

..  coq:: fold

  Definition Safe P :=
    forall state s l, ReachableFromBy initial_state state s l -> P state.

  Definition total_supply_tracks_correctly state :=
    sum (ERC20WrappedEth_wrapped (contract_state state))
      = (ERC20WrappedEth__totalSupply (contract_state state))
      /\ (forall key value, get_default 0 key
      (ERC20WrappedEth_wrapped (contract_state state)) 
        = value -> (value >= 0)).

  Theorem total_supply_correct : Safe total_supply_tracks_correctly.
  Proof.
  unfold Safe. intros. (* H *)
  induction H.
  - unfold total_supply_tracks_correctly.
    unfold initial_state. simpl.
    split.
    * unfold sum. unfold empty. unfold Int256Tree.fold1. simpl.
      reflexivity.
    * intros. unfold get_default in H. rewrite gempty in H.
      lia.
  - Hlinks.
    destruct prev; autounfold in *; simpl in *.
    destruct Step_action0; simpl in *.
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
    + Transparent ERC20WrappedEth_balanceOf_opt.
      unfold ERC20WrappedEth_balanceOf_opt in case_balanceOf_prf.
      ds_inv; subst; simpl in *.
      inversion case_balanceOf_prf.
      unfold total_supply_tracks_correctly.
      simpl.
      unfold total_supply_tracks_correctly in IHReachableFromBy.
      split.
      * apply IHReachableFromBy.
      * destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
        apply IHReachableFromByCorollary2.
    + Transparent ERC20WrappedEth_transfer_opt.
      unfold ERC20WrappedEth_transfer_opt in case_transfer_prf.
      destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
      clear H HL.
      ds_inv; subst; simpl in *.
      * unfold total_supply_tracks_correctly.
        simpl.
        unfold total_supply_tracks_correctly in IHReachableFromByCorollary1.
        rewrite <- IHReachableFromByCorollary1.
        apply (f_equal negb) in H9.
        rewrite negb_involutive in H9. simpl in H9.
        apply Int256eq_false in H9.
        split.
        -- Check Int256Tree_Properties.constant_sum'.
          apply Int256Tree_Properties.constant_sum'; try reflexivity. (* H9 *)
          assumption.
        -- intros.
          apply (f_equal negb) in H5. rewrite negb_involutive in H5.
          apply Int256eq_false in H5.
          destruct((caller context) =? key)%int256 eqn:SCase.
            ++ apply Int256eq_true in SCase. subst.
                rewrite get_default_ss.
                lia.
            ++ apply Int256eq_false in SCase. subst.
                rewrite get_default_so by auto.
                pose proof (IHReachableFromByCorollary2 (key) (get_default 0 (key)
                    (ERC20WrappedEth_wrapped (contract_state Step_state0)))).
                destruct(_to =? key)%int256 eqn:SSCase.
                  ** apply Int256eq_true in SSCase. subst.
                    rewrite get_default_ss.
                    lia.
                  ** apply Int256eq_false in SSCase. subst.
                    rewrite get_default_so by auto.
                    lia.
    + Transparent ERC20WrappedEth_transferFrom_opt.
      unfold ERC20WrappedEth_transferFrom_opt in case_transferFrom_prf.
      destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
      clear H HL.
      ds_inv; subst; simpl in *.
      * unfold total_supply_tracks_correctly.
        simpl.
        unfold total_supply_tracks_correctly in IHReachableFromByCorollary1.
        rewrite <- IHReachableFromByCorollary1.
        apply (f_equal negb) in H9.
        rewrite negb_involutive in H9. simpl in H9.
        apply Int256eq_false in H9.
        split.
        -- Check Int256Tree_Properties.constant_sum'. 
          apply Int256Tree_Properties.constant_sum'; try reflexivity.
          assumption.
        -- intros.
          apply (f_equal negb) in H5. rewrite negb_involutive in H5.
          apply Int256eq_false in H5.
          destruct(_from =? key)%int256 eqn:SCase.
            ++ apply Int256eq_true in SCase. subst.
                rewrite get_default_ss.
                lia.
            ++ apply Int256eq_false in SCase. subst.
                rewrite get_default_so by auto.
                pose proof (IHReachableFromByCorollary2 (key) (get_default 0 (key)
                    (ERC20WrappedEth_wrapped (contract_state Step_state0)))).
                destruct(_to =? key)%int256 eqn:SSCase.
                  ** apply Int256eq_true in SSCase. subst.
                    rewrite get_default_ss.
                    lia.
                  ** apply Int256eq_false in SSCase. subst.
                    rewrite get_default_so by auto.
                    lia.
    + Transparent ERC20WrappedEth_allowance_opt.
      unfold ERC20WrappedEth_allowance_opt in case_allowance_prf.
      ds_inv; subst; simpl in *.
      inversion case_allowance_prf.
      unfold total_supply_tracks_correctly.
      simpl.
      unfold total_supply_tracks_correctly in IHReachableFromBy.
      split.
      * apply IHReachableFromBy.
      * destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
        apply IHReachableFromByCorollary2.
    + Transparent ERC20WrappedEth_approve_opt.
      unfold ERC20WrappedEth_approve_opt in case_approve_prf.
      ds_inv; subst; simpl in *.
      inversion case_approve_prf.
      clear H HL case_approve_prf.
      destruct (_value >=? 0); simpl in *; inversion H1.
      unfold total_supply_tracks_correctly.
      simpl.
      apply IHReachableFromBy.
    + Transparent ERC20WrappedEth_approveSafely_opt.
      unfold ERC20WrappedEth_approveSafely_opt in case_approveSafely_prf.
      ds_inv; subst; simpl in *.
      inversion case_approveSafely_prf. 
      clear H HL case_approveSafely_prf.
      destruct (_value >=? 0); simpl in *; [|inversion H1].
      destruct (_currentValue =?
                  get_default 0 _spender
                    (get_default (empty Z) (caller context)
                      (ERC20WrappedEth_allowances (contract_state Step_state0)))); simpl in *.
      inversion H1.
      unfold total_supply_tracks_correctly. simpl. assumption.
      inversion H1.
      assumption.
      + Transparent ERC20WrappedEth_mint_opt.
      unfold ERC20WrappedEth_mint_opt in case_mint_prf.
      clear H HL.
      ds_inv; subst; simpl in *.
      * unfold total_supply_tracks_correctly.
        simpl.
        destruct IHReachableFromBy as
          [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
        unfold total_supply_tracks_correctly in IHReachableFromByCorollary1.
        split.
        -- unfold sum.
          Print sum.
          Check sum_set_x_minus_from_arbitrary_init.
          rewrite sum_set_x_minus_from_arbitrary_init with
            (v:=(get_default 0 (caller context)
              (ERC20WrappedEth_wrapped
                (contract_state Step_state0)))) by reflexivity.
          remember((get_default 0 (caller context)
            (ERC20WrappedEth_wrapped
              (contract_state Step_state0)))) as v.
          fold (sum (ERC20WrappedEth_wrapped (contract_state Step_state0))).
          rewrite <- IHReachableFromByCorollary1. 
          lia.
        -- intros.
            subst.
            pose proof (IHReachableFromByCorollary2 (caller context) (get_default 0 (caller context)
                (ERC20WrappedEth_wrapped (contract_state Step_state0)))).
            destruct((caller context) =? key)%int256 eqn:SCase.
              ++ apply Int256eq_true in SCase. subst.
                rewrite get_default_ss.
                lia.
              ++ apply Int256eq_false in SCase. subst.
                rewrite get_default_so by auto.
                pose proof (IHReachableFromByCorollary2 key (get_default 0 key
                (ERC20WrappedEth_wrapped (contract_state Step_state0)))).
                lia.
      + Transparent ERC20WrappedEth_burn_opt.
      unfold ERC20WrappedEth_burn_opt in case_burn_prf.
      clear H HL.
      ds_inv; subst; simpl in *.
      * unfold total_supply_tracks_correctly.
        simpl.
        destruct IHReachableFromBy as [IHReachableFromByCorollary1 IHReachableFromByCorollary2].
        unfold total_supply_tracks_correctly in IHReachableFromByCorollary1.
        split.
        -- unfold sum.
          rewrite sum_set_x_minus_from_arbitrary_init with
            (v:=(get_default 0 (caller context)
              (ERC20WrappedEth_wrapped
                (contract_state Step_state0)))) by reflexivity.
          remember((get_default 0 (caller context)
            (ERC20WrappedEth_wrapped
              (contract_state Step_state0)))) as v.
          fold (sum (ERC20WrappedEth_wrapped (contract_state Step_state0))).
          rewrite <- IHReachableFromByCorollary1. (* .no-in .unfold -* *)
          lia.
          -- intros.
          subst.
          pose proof (IHReachableFromByCorollary2 (caller context) (get_default 0 (caller context)
              (ERC20WrappedEth_wrapped (contract_state Step_state0)))).
          destruct((caller context) =? key)%int256 eqn:SCase.
            ++ apply Int256eq_true in SCase. subst.
              rewrite get_default_ss.
              lia.
            ++ apply Int256eq_false in SCase. subst.
              rewrite get_default_so by auto.
              pose proof (IHReachableFromByCorollary2 key (get_default 0 key
              (ERC20WrappedEth_wrapped (contract_state Step_state0)))).
              lia.
      * inversion Heqb.
    + rewrite <- HS. unfold total_supply_tracks_correctly. simpl. apply IHReachableFromBy.
    + rewrite <- HS. unfold total_supply_tracks_correctly. simpl. apply IHReachableFromBy.
    + rewrite <- HS. unfold total_supply_tracks_correctly. simpl. apply IHReachableFromBy.
  Qed.

.. coq:: none

  Opaque ERC20WrappedEth_totalSupply_opt.
  Opaque ERC20WrappedEth_balanceOf_opt.
  Opaque ERC20WrappedEth_transfer_opt.
  Opaque ERC20WrappedEth_transferFrom_opt.
  Opaque ERC20WrappedEth_approve_opt.
  Opaque ERC20WrappedEth_approveSafely_opt.
  Opaque ERC20WrappedEth_allowance_opt.
  Opaque ERC20WrappedEth_mint_opt.
  Opaque ERC20WrappedEth_burn_opt.

----

**Safety Property: Sufficient Funds Safe**

.. coq:: in

  Definition balance_backed state :=
    sum (ERC20WrappedEth_wrapped (contract_state state))
        <= (balance state contract_address).
  
  Theorem sufficient_funds_safe : Safe balance_backed.
  Proof. (* .in *)
  unfold Safe. (* .none *) intros. (* .none *)
  pose proof (total_supply_correct state s l H). (* .none *)
  unfold total_supply_tracks_correctly in H0. (* .none *)
  unfold balance_backed. (* .none *)
  destruct H0. (* .none *)
  rewrite H0. (* .none *)
  clear H0 H1. (* .none *)
  induction H.
  - simpl. (* .out .unfold -.h#* .h#snapshot_balances_valid_prf *)
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
      rewrite H2. (* .out .unfold -.h#* .h#IHReachableFromBy .h#H6 *)
      clear -IHReachableFromBy. (* .none *)
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
        rewrite H6. (* .out .unfold -.h#* .h#IHReachableFromBy .h#H2 *)
        clear -IHReachableFromBy H2. (* .none *)
        lia.
      * exfalso. (* .out .unfold -.h#* .h#Heqb *)
      inversion Heqb.
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
        rewrite <- Case. (* .out .unfold -.h#* .h#IHReachableFromBy .h#H *)
        clear -IHReachableFromBy H. (* .none *)
        lia.
      * (* .none *) destruct(sender =? recipient)%int256 eqn:SCase; try lia. (* .none *)
    + rewrite HS in *. apply IHReachableFromBy.
    + rewrite HS in *. apply IHReachableFromBy.  
  Qed.

.. coq:: none
  
  Opaque ERC20WrappedEth_totalSupply_opt.
  Opaque ERC20WrappedEth_balanceOf_opt.
  Opaque ERC20WrappedEth_transfer_opt.
  Opaque ERC20WrappedEth_transferFrom_opt.
  Opaque ERC20WrappedEth_approve_opt.
  Opaque ERC20WrappedEth_approveSafely_opt.
  Opaque ERC20WrappedEth_allowance_opt.
  Opaque ERC20WrappedEth_mint_opt.
  Opaque ERC20WrappedEth_burn_opt.

**Full proof**

.. coq:: fold

  Theorem sufficient_funds_safe' : Safe balance_backed.
  Proof.
  unfold Safe. intros.
  pose proof (total_supply_correct state s l H).
  unfold total_supply_tracks_correctly in H0.
  unfold balance_backed.
  destruct H0.
  rewrite H0.
  clear H0 H1.
  induction H.
  - simpl. (* snapshot_balances_valid_prf *)
    apply snapshot_balances_valid_prf.
  - Hlinks.
    destruct prev; autounfold in *; simpl in *.
    destruct Step_action0; simpl in *.
    + Transparent ERC20WrappedEth_totalSupply_opt.
      unfold ERC20WrappedEth_totalSupply_opt in case_totalSupply_prf.
      ds_inv; subst; simpl in *. 
      inversion case_totalSupply_prf.
      unfold new_balance_after_contract_call.
      pose proof (NoLeftoverOutgoings H).
      rewrite H0.
      unfold current_balances, update_balances.
      rewrite Int256.eq_true.
      destruct((caller context) =? contract_address)%int256 eqn:Case.
      * apply IHReachableFromBy.
      * rewrite Int256.eq_sym.
        rewrite Case.
        lia.
    + Transparent ERC20WrappedEth_balanceOf_opt.
      unfold ERC20WrappedEth_balanceOf_opt in case_balanceOf_prf.
      ds_inv; subst; simpl in *. 
      inversion case_balanceOf_prf.
      unfold new_balance_after_contract_call.
      pose proof (NoLeftoverOutgoings H).
      rewrite H0.
      unfold current_balances, update_balances.
      rewrite Int256.eq_true.
      destruct((caller context) =? contract_address)%int256 eqn:Case.
      * apply IHReachableFromBy.
      * rewrite Int256.eq_sym.
        rewrite Case.
        lia.
    + Transparent ERC20WrappedEth_transfer_opt.
      unfold ERC20WrappedEth_transfer_opt in case_transfer_prf.
      pose proof (NoLeftoverOutgoings H).
      clear HL H.
      ds_inv; subst; simpl in *. 
      unfold new_balance_after_contract_call.
      simpl.
      rewrite H0.
      unfold current_balances, update_balances.
      rewrite Int256.eq_true.
      destruct((caller context) =? contract_address)%int256 eqn:Case.
      * apply IHReachableFromBy.
      * rewrite Int256.eq_sym.
        rewrite Case.
        lia.
    + Transparent ERC20WrappedEth_transferFrom_opt.
      unfold ERC20WrappedEth_transferFrom_opt in case_transferFrom_prf.
      pose proof (NoLeftoverOutgoings H).
      clear HL H.
      ds_inv; subst; simpl in *. 
      unfold new_balance_after_contract_call.
      simpl.
      rewrite H0.
      unfold current_balances, update_balances.
      rewrite Int256.eq_true.
      destruct((caller context) =? contract_address)%int256 eqn:Case.
      * apply IHReachableFromBy.
      * rewrite Int256.eq_sym.
        rewrite Case.
        lia.
    + Transparent ERC20WrappedEth_allowance_opt.
      unfold ERC20WrappedEth_allowance_opt in case_allowance_prf.
      pose proof (NoLeftoverOutgoings H).
      clear HL H.
      ds_inv; subst; simpl in *. 
      unfold new_balance_after_contract_call.
      simpl.
      rewrite H0.
      unfold current_balances, update_balances.
      rewrite Int256.eq_true.
      destruct((caller context) =? contract_address)%int256 eqn:Case.
      * apply IHReachableFromBy.
      * rewrite Int256.eq_sym.
        rewrite Case.
        lia.
    + Transparent ERC20WrappedEth_approve_opt.
      unfold ERC20WrappedEth_approve_opt in case_approve_prf.
      pose proof (NoLeftoverOutgoings H).
      clear HL H.
      ds_inv; subst; simpl in *. 
      unfold new_balance_after_contract_call.
      simpl.
      rewrite H0.
      unfold current_balances, update_balances.
      rewrite Int256.eq_true.
      destruct((caller context) =? contract_address)%int256 eqn:Case.
      * apply IHReachableFromBy.
      * rewrite Int256.eq_sym.
        rewrite Case.
        lia.
    + Transparent ERC20WrappedEth_approveSafely_opt.
      unfold ERC20WrappedEth_approveSafely_opt in case_approveSafely_prf.
      pose proof (NoLeftoverOutgoings H).
      clear HL H.
      ds_inv; subst; simpl in *. 
      * unfold new_balance_after_contract_call.
        simpl.
        rewrite H0.
        unfold current_balances, update_balances.
        rewrite Int256.eq_true.
        destruct((caller context) =? contract_address)%int256 eqn:Case.
        -- apply IHReachableFromBy.
        -- rewrite Int256.eq_sym.
          rewrite Case.
          lia.
      * unfold new_balance_after_contract_call. simpl. rewrite H0.
        unfold current_balances, update_balances.
        rewrite Int256.eq_true.
        destruct((caller context) =? contract_address)%int256 eqn:Case.
        -- apply IHReachableFromBy.
        -- rewrite Int256.eq_sym.
          rewrite Case.
          lia.
    + Transparent ERC20WrappedEth_mint_opt.
      unfold ERC20WrappedEth_mint_opt in case_mint_prf.
      pose proof (NoLeftoverOutgoings H).
      clear HL H.
      ds_inv; subst; simpl in *. 
      unfold new_balance_after_contract_call.
      simpl.
      rewrite H0.
      unfold current_balances, update_balances.
      rewrite Int256.eq_true.
      apply (f_equal negb) in H2. rewrite negb_involutive in H2.
      simpl in H2.
      rewrite H2.
      rewrite Int256.eq_sym in H2.
      rewrite Z.gtb_lt in H6.
      rewrite H2. (* IHReachableFromBy H6 *)
      clear -IHReachableFromBy.
      lia.
    + Transparent ERC20WrappedEth_burn_opt.
      unfold ERC20WrappedEth_burn_opt in case_burn_prf.
      pose proof (NoLeftoverOutgoings H).
      clear HL H.
      ds_inv; subst; simpl in *. 
      * 
        unfold new_balance_after_contract_call.
        simpl.
        unfold current_balances, update_balances.
        rewrite Int256.eq_true.
        apply (f_equal negb) in H6. rewrite negb_involutive in H6.
        simpl in H6.
        rewrite H6.
        rewrite Int256.eq_sym in H6.
        rewrite Z.geb_le in H2.
        rewrite Z.eqb_eq in H10. rewrite H10.
        rewrite Z.add_0_r, Z.sub_0_r.
        rewrite Z.geb_le in H16.
        rewrite H6. (* IHReachableFromBy H2 *)
        clear -IHReachableFromBy H2.
        lia.
      * exfalso. (* Heqb *)
      inversion Heqb.
    + unfold current_balances, update_balances.
      destruct prf.
      clear H HL.
      apply Int256.eq_false in n.
      rewrite Int256.eq_sym in n.
      rewrite n.
      rewrite HS in *.
      destruct(contract_address =? recipient)%int256 eqn:Case.
      * destruct(sender =? recipient)%int256 eqn:SCase; try lia.
        destruct a.
        apply Int256eq_true in Case.
        rewrite <- Case. (* IHReachableFromBy H *)
        clear -IHReachableFromBy H.
        lia.
      * destruct(sender =? recipient)%int256 eqn:SCase; try lia.
    + rewrite HS in *. apply IHReachableFromBy.
    + rewrite HS in *. apply IHReachableFromBy.  
  Qed.

.. coq:: none

  End Blockchain_Model.

  End FunctionalCorrectness.

----

Formal Verification Effort
==========================

.. image:: effort1.png

.. image:: effort2.png

----

**References**

- Slides powered by Alectryon_: https://github.com/cpitclaudel/alectryon (Also supports Lean 4!)
- The DeepSEA compiler is partly based upon the CompCert_ Verified Compiler
- My papers: https://academic.danielb.space
- C DeepSEA paper: https://dl.acm.org/doi/pdf/10.1145/3360562
- Verified Price Oracles paper: https://doi.org/10.4230/OASIcs.FMBC.2021.1
- arXiv DeepSEA paper: https://arxiv.org/abs/2405.08348

- GitHub links:
    - DeepSEA_
    - My DeepSEA fork_ 
    - The Crowdfunding_ contract
    - Source code for these slides_

.. _Alectryon: https://github.com/cpitclaudel/alectryon
.. _CompCert: https://compcert.org/
.. _DeepSEA: https://github.com/ShentuChain/deepsea
.. _fork: https://github.com/Coda-Coda/deepsea-1
.. _Crowdfunding: https://github.com/Coda-Coda/Crowdfunding/
.. _slides: https://github.com/Coda-Coda/DeepSEA-ERC20-Talk

----

============
Extra Slides
============

----

===============
Paper overviews
===============

----

.. image:: arxiv-paper.png
  :target: https://arxiv.org/abs/2405.08348

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
