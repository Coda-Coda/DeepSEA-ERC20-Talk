:title: Untangling mechanized proofs
:css: talk.css
:css: alectryon.css
:css: tango_subtle.css
:js-body: talk.js
:js-body: alectryon.js
:slide-numbers: true
:data-transition-duration: 0.01
:alectryon/serapi/args: -Q /home/clement/git/alectryon/talk/coq/ ""

.. :auto-console: true

----

.. container:: titlepage

   .

==============================
 Untangling mechanized proofs
==============================

Clément Pit-Claudel
===================

SLE 2020 / SPLASH 2021
----------------------

.. note::

   .

----

=====================
 A tour of Alectryon
=====================

.. note::

   Back in undergrad I taught in high school for a few months. There was a proof I liked to show my students, because it surprised most of them.

----

.. raw:: html

   <script type="text/javascript">
     MathJax = {
         options: {
             skipHtmlTags: [
                 'script', 'noscript', 'style', 'textarea',
                 'annotation', 'annotation-xml'
             ]
         },
         startup: {
             pageReady: function () {
                 mathjax_setup();
                 return MathJax.startup.defaultPageReady();
             }
         }
     };
   </script>

   <script type="text/javascript" id="MathJax-script" async
      src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js">
   </script>

.. container:: xxxxl

   .. math:: \frac{a}{c} + \frac{b}{d} \not= \frac{a + b}{c + d}

.. note::

   This was the setup: every student knows that you can't sum fractions element-wise.
   What many students don't know is that you *can*, actually, as long as long you're just trying to prove an inequality.

----

.. container:: xxxxl

   .. math:: \frac{a}{c} + \frac{b}{d} \ge \frac{a + b}{c + d}

.. note::

   My main line of research is doing proofs with the Coq proof assistant, so let me share a Coq proof of this inequality.

----

.. raw:: html

   <div style="display: none">
       \(\newcommand{\ccQ}{\mathbb{Q}}\)
       \(\newcommand{\ccNat}{\mathbb{N}}\)
       \(\newcommand{\ccSucc}[1]{\mathrm{S}\:#1}\)
       \(\newcommand{\ccFrac}[2]{\frac{#1}{#2}}\)
       \(\newcommand{\ccPow}[2]{{#1}^{#2}}\)
       \(\newcommand{\ccNot}[1]{{\lnot #1}}\)
       \(\newcommand{\ccEvar}[1]{\textit{\texttt{#1}}}\)
       \(\newcommand{\ccForall}[2]{\forall \: #1. \; #2}\)
       \(\newcommand{\ccNsum}[3]{\sum_{#1 = 0}^{#2} #3}\)
   </div>

.. container:: proof-overlay

   .. code:: coq

      Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
        (a + c)/(b + d) ≤ a/b + c/d.
      Proof with Qeauto.
        intros a b c d H.
        field_simplify...
        rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact...
        rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
        field_simplify.
        rewrite <- (Qminus_le_l (b * d * a)); ring_simplify.
        rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
        Qeauto using Qsqr_0.
      Qed.

   .. class:: substep

      .. image:: coq.png
         :class: rooster-sticker

.. note::

   Statement at top, Qed at bottom, all good?

   How about with a little rooster to the side, convinced now?

   Show of hands: who learnt something deep from looking at this "proof"?

   Proof *script*.  Sequence of steps/tactics like multiply both sides, from premises to conclusion.

   Not what mathematicians call “a proof”.
   Missing *goals*, …. That's because computed.

----

.. image:: coqide.png
   :alt: CoqIDE showing a proof script and a goal.
   :class: img-m

.. note::

   Of course states redundant, in a sense.  But downside: reading a proof script is impossible.


   Sometimes don't why proof is true.  E.g. program properties, or large enumeration of cases.  Coq happy I'm happy.

   But sometimes there's content.  Interesting info.
   Want to show not just steps, goals.

   If readers have Coq installed, OK.
   But sometimes not right version, or proof has dependencies, or compilation slow, or mobile phone, or browsing casually, or… writing book!

   So what do people do to write manuals, tutorials, textbooks, blog posts, or any other piece of text that mixes Coq proofs and prose?

----

.. code:: coq

   Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
     (a + c)/(b + d) ≤ a/b + c/d.
   Proof with Qeauto.
     intros a b c d H.
     (** [(a + c) / (b + d) ≤ a / b + c / d] *)
     field_simplify...
     (** [(a + c) / (b + d) ≤ (a * d + c * b) / (b * d)] *)
     rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact...
     rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
     (** [b * d * (a + c) ≤ (b + d) * (a * d + c * b)] *)
     field_simplify.
     (** [b * d * a + b * d * c ≤ b ^ 2 * c + b * d * a + b * d * c + d ^ 2 * a] *)
     rewrite <- (Qminus_le_l (b * d * a)); ring_simplify.
     rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
     (** [0 ≤ b ^ 2 * c + d ^ 2 * a] *)
     Qeauto using Qsqr_0.
   Qed.

.. note::

   In most cases they do something like this: they run the proof in Coq and then, by hand, they copy the output of each tactic into source code comments.

----

.. code:: coq

   Require Import Arith.
   Print fact.
   (** [[
   fact =
   fix fact (n : nat) : nat :=
     match n with
     | 0 => 1
     | S n0 => S n0 * fact n0
     end
        : nat -> nat
   ]]
   *)

(CPDT)

.. note::

   Here's what it looks like in Certified Programming with Dependent Types.

----

.. code:: coq

   pose D x := if x is 2 then False else True.

   (**
   [[
     H : 2 === 1
     D := fun x : nat =>
          match x with
          | 0 => True
          | 1 => True
          | 2 => False
          | S (S (S _)) => True
          end : nat -> Prop
     ============================
      False
   ]] **)

(Programs and Proofs)

.. note::

   Here's what it looks like in Illya's Programs and Proofs.

----

.. code:: coq

   Print Assumptions function_equality_ex2.
   (* ===>
        Axioms:
        functional_extensionality :
            forall (X Y : Type) (f g : X -> Y),
                   (forall x : X, f x = g x) -> f = g *)

(Software foundations)

.. note::

   Here's what it looks like in Software Foundations.

   Super cumbersome.  Lots of work, lots of mistakes.
   Copy pasted output gets out of sync — we all know even high level comments get out of sync fast.

   Wait for readers to find the issues.

   There's got to be a better way, and that's where Alectryon comes in.

   Alectryon two things:

   1. Compiler: captures Coq output and interleaves it in original proof script as webpage.
   2. Literate programming system for Coq.


----

.. container:: alectryon-block

   .. coq:: unfold no-hyps

      Require Import Qle. (* .none *)
      Module Ex1. (* .none *)
      Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
        (a + c)/(b + d) ≤ a/b + c/d. (* .fold *)
      Proof with Qeauto. (* .fold *)
        intros a b c d H.
        field_simplify...
        rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact... (* .fold *)
        rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
        field_simplify.
        rewrite <- (Qminus_le_l (b * d * a)); ring_simplify. (* .fold *)
        rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
        Qeauto using Qsqr_0.
      Qed.
      End Ex1. (* .none *)

.. note::

   Here's the same proof.  Took file, fed Coq, collected output, formatted, and generated interactive visualization.

   Interactive webpage; every proof step is button that reveals proof state.

   After every change can rerun Alectryon and regen the page.

   Outputs recorded, all static: no need to load Coq.

   Everything is web technologies → flexible rendering.

----

.. container:: coq-mathjax

   .. coq:: unfold no-hyps

      Module Ex3. (* .none *)
      Import LatexNotations. (* .none *)
      Lemma Qle_pairwise : ∀ a b c d, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d →
        (a + c)/(b + d) ≤ a/b + c/d. (* .fold *)
      Proof with Qeauto. (* .fold *)
        intros a b c d H.
        field_simplify...
        rewrite <- (Qmult_le_l (b + d)), Qmult_div_r, Qmult_Qdiv_fact... (* .fold *)
        rewrite <- (Qmult_le_l (b * d)), Qmult_div_r...
        field_simplify.
        rewrite <- (Qminus_le_l (b * d * a)); ring_simplify. (* .fold *)
        rewrite <- (Qminus_le_l (b * d * c)); ring_simplify.
        Qeauto using Qsqr_0.
      Qed.
      End Ex3. (* .none *)
      Open Scope nat_scope. (* .none *)

.. note::

   Use web tech to give meaningful rendering.
   Good shot at understanding: sum fracs, same denominator, cancel, greater than 0

..
   ----

   .. coq:: unfold

      Lemma Gauss: ∀ n, 2 * (sum n) = n * (n + 1). (* .fold *)
      Proof. (* .fold *)
        induction n. (* .fold *)
        - (* n ← 0 *)
          reflexivity.
        - (* n ← S _ *)
          cbn [sum].
          rewrite Mult.mult_plus_distr_l.
          rewrite IHn.
          ring_simplify.
          reflexivity.
      Qed.

   .. note::

      Here's what it looks on another simple proof, forgetting about the fancy LaTeX stuff for a moment.

----

.. coq::

   Section classical. (* .none *)
     Context (excl: ∀ A, A ∨ ~ A).
     Goal ∀ A, ¬¬A → A.
       intros A notnot_A. (* .in *)
       Show Proof. (* .messages .unfold *)
       destruct (excl A) as [a | na]. (* .in *)
       Show Proof. (* .messages .unfold *)
       - assumption. (* .in *)
         Show Proof. (* .messages .unfold *)
     Abort. (* .none *)
   End classical. (* .none *)

.. note::

   Here's different example of using Alectryon to help readers develop better understanding.

   And that's what first part of Alectryon is about!  Alectryon automatically annotates proof scripts with Coq's output, generating a complete record of the proof that captures the intermediate proof states and renders them.

----

.. coq::

   (** So far, it looks like co-inductive types might be a magic
       bullet, allowing us to import all of the
       Haskeller's usual tricks. …

       The restriction for co-inductive types shows up as
       the%\index{guardedness condition}% _guardedness
       condition_.  First, consider this stream definition,
       which would be legal in Haskell.

       [[
       CoFixpoint looper : stream nat := looper.
       ]]

       <<
       Error:
       Recursive definition of looper is ill-formed.
       In environment
       looper : stream nat
       unguarded recursive call in "looper"
       >> **)

.. note::

   OK, so this solves 1 problem: displaying goals and outputs.
   But there's another aspect of writing about Coq proofs: the explanatory prose.

   There's no code here: it's all prose, embedded in source code comments.

   Lots of respect.  Whole other level of determination and grit to edit whole book in comments.

----

.. code:: coq

   (*|
   A fairly common occurrence when working with dependent
   types in Coq is to call `Compute` on a benign expression
   and get back a giant, partially-reduced term, like this:
   |*)

   Import EqNotations Vector.VectorNotations.
   Compute (hd (rew (Nat.add_1_r 3)
                    in ([1; 2; 3] ++ [4]))). (* .unfold *)

   (*|
   This post shows how to work around this issue.
   |*)

.. note::

   Shouldn't have to be this way; I want to use a text editor for text, and a code editor for code.

   Alectryon solves this by allowing you to toggle between views of your code.

   First looks very similar; but then I can switch to “prose mode”.
   Uses reStructuredText, very popular.
   Switch back.

   In prose mode get completion of english words, spellchecking, live preview.
   In code mode get Proof General experience, ITP.

----

.. code:: rst

   A fairly common occurrence when working with dependent
   types in Coq is to call `Compute` on a benign expression
   and get back a giant, partially-reduced term, like this:

   .. coq::

      Import EqNotations Vector.VectorNotations.
      Compute (hd (rew (Nat.add_1_r 3)
                       in ([1; 2; 3] ++ [4]))). (* .unfold *)

   This post shows how to work around this issue.

.. note::

   This is what it looks like after flipping the code and the prose around.  The syntax is reStructuredText.  reStructuredText is a great markup language, very much like Markdown but with a robust story for writing extensions; in fact, I used this whole presentation is just one large Coq file; I used Alectryon to convert it to reStructuredText.

   The best part is that you can go back: once you're done editing the prose of your document and you're ready to resume hacking on the proofs, you can use Alectryon to convert the reStructuredText file back into a Coq source file, in which the prose is wrapped in special comments and the code is at the top level.  Here, let's go back to the original code.

----

.. image:: emacs-screenshot.svg
   :alt: A screenshot of Emacs shows the same snippet from Software foundations, in code and prose views.


.. note::

   These two transformations are the inverse of one another, so you can switch between the code-oriented view and the prose-oriented view at will.  This is trivial to integrate into an IDE; I did it for Emacs, and I'm sure it would be very easy to do in any other editor.

   Being able to go back and forth between reStructuredText and Coq means that Alectryon does not have to implement its own markup language for literate comments: it can just piggyback on the existing reStructuredText toolchain, which is very robust and used by a lot of people for all sorts of documents, like the reference manuals of Python, Agda, Haskell, and a host of other languages — including Coq.

----

.. role:: red
   :class: red

.. role:: green
   :class: green

.. container:: xxxl

   :red:`✗` LaTeX ← literate document → Coq

   :green:`✓` reST ⇆ Coq

.. note::

   If you know literate, you might be confused.
   Normally tangling and weaving.
   There's a main document that you edit, then two views that you generate.
   Can't edit those.

   Not too bad except tooling for regular languages.

   Unusable for Coq: need interactive UI.  Hence all proof-heavy books written as Coq files.

   Alectryon is different: no main document, just tangled and weaved, and bidirectional conversion.  Chose which one to work with as needed.

----

================
 Implementation
================

.. container:: s

   Generate an interactive webpage from a literate Coq file with reST comments (Coqdoc style):
      .. code::

         ../alectryon.py literate.v

   Generate an interactive webpage from a plain Coq file (Proof General style):
      .. code::

         ../alectryon.py --frontend coq plain.v

   Generate an interactive webpage from a Coqdoc file (compatibility mode):
      .. code::

         ../alectryon.py --frontend coqdoc literate.v

   Compile a reStructuredText document containing ``.. coq::`` blocks (coqrst style):
      .. code::

         ../alectryon.py literate.v.rst

   Translate a reStructuredText document into a literate Coq file:
      .. code::

         ../alectryon.py literate.v.rst -o literate.v

   Translate a literate Coq file into a reStructuredText document:
      .. code::

         ../alectryon.py literate.v -o literate.v.rst

   Record goals and responses for fragments contained in a JSON source file:
      .. code::

         ../alectryon.py fragments.json

   Record goals and responses and format them as HTML for fragments contained in a JSON source file:
      .. code::

         ../alectryon.py fragments.json -o fragments.snippets.html

.. note::

   Now that I've given you a sense of what Alectryon does, let me say a bit about how it does it.

   Alectryon is a Python program, and it's written as a collection of mostly independent modules:

----

.. coq:: unfold

   (* Can you favorite IDE handle this?
      (mine can't, and I'm one of the maintainers…) *)
   Notation "( a . b )" := (a, b).
   Check (0 . 1).

.. note::

   Coq frontend.

----

.. container:: coq-mathjax

   .. coq:: unfold

      Module Gauss. (* .none *)
      Import LatexNotations. (* .none *)
      Lemma Gauss: ∀ n, 2 * (nsum n (fun i => i)) = n * (n + 1).
      Proof. (* .fold *)
        induction n; cbn [nsum]. (* .fold *)
        - (* n ← 0 *)
          reflexivity.
        - (* n ← S _ *)
          rewrite Mult.mult_plus_distr_l. (* .no-hyps *)
          rewrite IHn. (* .no-hyps *)
          ring.
      Qed.
      End Gauss. (* .none *)

.. note::

   Transforms to post-process Coq's output; either in Python or later in JS.

----

.. raw:: html

   <script src="https://d3js.org/d3.v5.min.js" charset="utf-8"></script>
   <script src="https://dagrejs.github.io/project/dagre-d3/latest/dagre-d3.js"></script>

.. container:: rbt-no-printing

   .. coq::

      Require Import RBT. (* .none *)
      Module RBT1. (* .none *)
      Definition build_trees (leaves: list nat) :=
        List.fold_left (fun trs n => RBT.add n (hd RBT.empty trs) :: trs)
          leaves [] |> List.rev.

      Compute build_trees [1;2;3;4;5]. (* .unfold *)
      Compute build_trees [2;1;4;3;6].
      End RBT1. (* .none *)

.. note::

   Concrete example: understand red-black trees.

----

.. container:: rbt-render

   .. coq::

      Module RBT2. (* .none *)
      Import RBTNotations. (* .none *)
      Definition build_trees (leaves: list nat) :=
        List.fold_left (fun trs n => RBT.add n (hd RBT.empty trs) :: trs)
          leaves [] |> List.rev.

      Compute build_trees [1;2;3;4;5]. (* .unfold *)
      Compute build_trees [2;1;4;3;6]. (* .unfold *)
      End RBT2. (* .none *)

.. note::

   Now with graphs!

----

.. image:: udiv.opt.paths.svg
   :alt: A piece of Coq code showing a binary object rendered by passing it to objdump and highlighting the result.

.. note::

   Second example: objdump.

----

.. image:: rss.paths.svg
   :class: img-m

.. note::

   Another component: HTML export.  Careful to use the right web tech to support wide range of use cases, including RSS feeds.

----

.. code:: coq

   Check "Where does this string (|* end? ".
   (*| And where does `"this comment *|)` end?" |*)
   Check "here? *)".

.. code:: rst

   .. coq::

      Check "Where does this string (|* end? ".

   And where does `"this comment *|)` end?"

   .. coq::

      Check "here? *)".

.. note::

   Then literate module to weave and tangle back and forth.
   Must keep track of positions, so keep context when switching views.

----

.. image:: sphinx.png
   :class: img-m

.. note::

   Finally connect to reStructuredText or Markdown pipelines with Docutils and Sphinx.

----

============
 Evaluation
============

.. note::

   The paper has a lot of evaluation, and I encourage you to check it out if you're curious; in brief, the evaluation is organized around two axes:

----

.. image:: polymorphic-universes-8-12.svg
   :class: img-m

.. note::

   First axis: robustness.  Compiled hundreds of thousands of lines of Coq code, all of standard library, books, tutorials: it works.  Even compiled entire first volume of Software foundations.

   Confusing!  I said reST but SF is coqdoc.  Actually example of extensibility.  Using coqdoc as markup language for prose, and code with Alectryon.

----

.. container:: twocolumns

   .. image:: stdlib.paths.svg
      :class: img-stdlib

   .. image:: breakdowns.paths.svg
      :class: img-breakdowns

.. note::

   The second axis measures Alectryon's speed.  All the graphs are in the paper, but the long story short is that Alectryon has a median overhead of 3x on compilation times (90% of all files fall below 7x), and a good 1/3 of that is communication overhead that can probably be eliminated in the future.  The rest is the overhead of collecting and formatting goals, which can be pretty costly for files that have a many goals.

----

==============
 Related work
==============

.. image:: citations.paths.svg

.. note::

   It's hard to do justice to all the related work in this area in just a few minutes, so I'll simply say that Alectryon builds on decades of great ideas for making programs and proofs more understandable, all the way from a paper in 1980 co-authored by Eric Schmidt and Phil Wadler to PhD theses written just a year ago.  There's 60 citations and three pages of related work in the paper; if you're curious about the history of this stuff, you should really have a look.

----

.. container:: xxxl

   | `<https://github.com/cpitclaudel/alectryon/>`__
   | `<https://alectryon-paper.github.io/>`__

.. note::

   To recap, Alectryon provides an architecture to record and visualize Coq proofs, facilitating sharing and interactive exploration of proof scripts; and a bidirectional translator between woven and tangled documents, enabling seamless editing of prose and code.

   Alectryon is freely available on GitHub, and it's received great reception from the community.

----

.. container:: xxxxl

   .. math:: \LaTeX

.. note::

   Maybe I can conclude with a few words about the next steps.  Here are some directions that I'm exploring or would like help exploring.
   First, I'd like to make a LaTeX backend: reStructuredText can produce LaTeX in addition to HTML, so it would make sense to support that as well.  I have a branch for this, and it's almost ready.

----

.. image:: life.svg

.. note::

   Second, I'd like to explore advanced visualizations further.  There are many domains for which the natural visualization for a piece of data is not text.  I have a few examples in the paper, but I'd like to push that idea further.  In fact, what would be really neat would be to settle on a standard for Coq developments to specify how to render a particular type.  I'm thinking of display-only notations that would produce images, graphs, plots, etc.  Once we have this, we could even integrate it with IDEs and finally stop envying the Racket folks with their magic picture tricks.

----

.. coq:: none

   Require Import String.
   Inductive Prog :=
   | Boring0
   | Boring1
   | Bind (var: string) (expr: Prog) (body: Prog)
   | Boring2
   | Boring3.

   Inductive Value: Type :=
     BoringValue.

   Inductive ComputesTo : Prog -> Value -> Prop :=
   | ComputesToAny : forall p v, ComputesTo p v.

   Definition context := list (string * Value).

   Require Import Lists.List.
   Import ListNotations.

   Fixpoint interp (gamma: context) (p: Prog) :=
     match p with
     | Bind var expr body => let val := interp gamma expr in interp ((var, val) :: gamma) body
     | _ => BoringValue
     end.

   Tactic Notation "t" := constructor.
   Tactic Notation "…" := constructor.

.. coq::

   Lemma interp_sound: forall (p: Prog) (gamma: context) (v: Value),
       ComputesTo p (interp gamma p).
   Proof.
     induction p; intros.
     - t.
     - t.
     - simpl. (* .unfold *)
       ….
     - t.
     - t.
   Qed.

.. note::

   Third, for all the machine learning wizards out there, I'd like to explore automatic proof summarization — just like automatically identifying the most exciting moments of a soccer game, but for Coq proofs.  More formally, the task is to automatically identify a small subset of proof steps that lead to particularly interesting or relevant goals; we'd use this in combination with Alectryon to identify the most interesting parts of a proof development.

----

.. image:: provers.svg

.. note::

   Finally, I'd like to extend the system to other languages, both for the markup side and for the Coq side.  I built Alectryon with Coq and reStructuredText, but very little of it is actually Coq or reStructuredText specific.

   To port Alectryon to a different language, like Lean for example, you would need to add a Python module that invokes Lean and collects its output, and if you also wanted the literate programming support you'd want to make a bidirectional translator for Lean's comment syntax.

   The literate programming parts were actually inspired by work that I did for F* a few years ago, so adding new languages really shouldn't be too hard.  If you're interested in getting Alectryon to work with your favorite proof assistant, please get in touch.

----

.. container:: xxxl

   | `<https://github.com/cpitclaudel/alectryon/>`__
   | `<https://alectryon-paper.github.io/>`__

.. note::

   Thanks for your attention!  Feel free to reach out if you have questions, and check the README and the paper for lots of extra info.
