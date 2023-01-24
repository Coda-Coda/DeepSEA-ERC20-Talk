:title: Provably Correct Smart Contracts using DeepSEA
:css: talk.css
:css: alectryon.css
:css: tango_subtle.css
:js-body: alectryon.js
:slide-numbers: true
:data-transition-duration: 0.01

.. :auto-console: true

----

==============================================
Provably Correct Smart Contracts using DeepSEA
==============================================

Daniel Britten
==============

Ethereum Engineering Group 2023
-------------------------------

.. note::

  It's great to be here...

----

=======
DeepSEA
=======

----

.. coq::

  Check nat. (* .unfold *)


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
    | advance _ _ =>
      match s with
      | initial => middle
      | middle => final
      | extra => middle
      | final => _
      end
    | sidetrack _ _ =>
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

----

================================
Modelling a Blockchain using Coq
================================