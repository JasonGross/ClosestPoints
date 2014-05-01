(** * 1-D Closest Point Algorithm *)
Require Import Ascii String Sorted FMapAVL Wf Wf_nat.
Require Import Utf8 List.
Require Import CommonDefinitions.

Set Implicit Arguments.
Generalizable All Variables.

Local Open Scope list_scope.
Local Open Scope string_scope.

(** ** Motivation *)
(** "When doing formal program verification, take the simplest
     non-trivial relevant example.  Then take a simpler example, and
     formalize that." -- paraphrase of Adam Chlipala on best practices
     in program synthesis and verification *)

Require Import Algorithm.BruteForce.

(** ** Now we implement the axtual algorithm. *)

(** ** A type of points *)
Require Import Point.Core.

(** ** The strip around the median *)
Require Import CenterStrip.Core.

(** ** A set of points *)
Require Import PointSet.Core.

(** ** The tree with data *)
Require Import Tree.

(** ** The core algorithm *)
Require Import Algorithm.Core.

(** ** Split markers *)
Require Import SplitMarker.Core.

(** ** Naïve Point Set *)
Require Import PointSet.Naive.

(** ** The display mechanism *)
Require Import Printers.Nat.
Import NatPrinter.
Require Import Printers.Helpers.

(** ** The full algorithm *)
Require Import Algorithm.Full1D.

Notation results := (focus _).

Goal True.
  pose (0::2::5::3::15::22::20::12::10::(*25::*)[])%list as points.
  assert (p : focus (make_display_from_list points)) by exact focusI.
  lazy in p.
  assert (n : focus 0) by exact focusI.

  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.
  next p n.


Abort.
