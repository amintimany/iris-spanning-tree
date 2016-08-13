From iris.program_logic Require Export global_functor.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
Import uPred.

Definition try_mark : val :=
  λ: "y",
  let: "e" := ! "y" in CAS "y" (#false, Snd "e") (#true, Snd "e").

Definition unmark_fst : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (#true, (NONE, Snd (Snd "e"))).

Definition unmark_snd : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (#true, (Fst (Snd "e"), NONE)).

Definition span : val :=
  rec: "span" "x" :=
  match: "x" with
    NONE => # false
  | SOME "y" =>
    if: try_mark "y" then
      let: "e" := ! "y" in
      let: "rs" := "span" (Fst (Snd "e")) || "span" (Snd (Snd "e")) in
      (if: ~ (Fst "rs") then unmark_fst "y" else #())
        ;; if: ~ (Fst "rs") then unmark_fst "y" else #()
    else
      #false
  end.