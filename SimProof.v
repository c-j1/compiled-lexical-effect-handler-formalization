From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.
From LSEH Require Import LexiToSalt.

(* Initial & Final Predicates for Lexi and Salt *)

(* Observable Behaviour *)
  (* Converge, Stuck, Diverge *)
Inductive ob : Prop :=