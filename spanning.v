From iris.algebra Require Import frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre tactics.
From iris.program_logic Require Export global_functor.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Export lifting heap notation.
From iris.heap_lang.lib Require Import par.
Import uPred.

From iris_spanning_tree Require Import graph mon.

Definition try_mark : val :=
  λ: "y", let: "e" := Fst (!"y") in CAS "e" #false #true.

Definition unmark_fst : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (Fst "e", (NONE, Snd (Snd "e"))).

Definition unmark_snd : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (Fst "e", (Fst (Snd "e"), NONE)).

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

  (* This change should happen in iris. -- to allow _ in the context with
which we are binding. *)
  Local Tactic Notation "wp_bind" open_constr(K) :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|fast_by apply (wp_bind K)]; simpl
  end.

  Ltac open_graph_inv Hinv key γ mr pat :=
    let HIK := eval cbv in ("[" +:+ Hinv +:+ " " +:+ key +:+ "]") in
    iDestruct (UnPack_later with HIK) as HIK;
    [iNext; iSplitL key; by iFrame|];
    rewrite {2}/graph_inv later_exist; iDestruct Hinv as (γ) Hinv;
    rewrite later_exist; iDestruct Hinv as (mr) Hinv;
    iDestruct Hinv as pat.


Section Helpers.
  Context {Σ} {Ih : heapG Σ} {Im : markingG Σ} {Ig : graphG Σ} {Ii : invtokG Σ}.

  Lemma wp_try_mark g Mrk k q (x : loc) w :
    marked g = ∅ →
    (heap_ctx ★ graph_ctx g Mrk ★ Γρ(q, x [↦] w) ★ κ(k))
      ⊢
      WP (try_mark #x)
      {{ v,
         match v with
         | # true =>
           (∃ u, (w = None)
                   ★ ((g !! x) = Some (false, u)) ★
                   Γρ(q, x [↦] Excl' u))
         | # false => Γρ(q, x [↦] w)
         | _ => False
         end
           ★ μ(x) ★ κ(k)
      }}.
  Proof.
    intros Hgnm. iIntros "(#Hheap & #Hgr & Hx & key)". unfold try_mark.
    wp_let; wp_focus (! _)%E. unfold graph_ctx; iInv graphN as "Hinv".
    open_graph_inv "Hinv" "key" γ mr "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5)".
    iDestruct (graph_open_later with "[Hx Hi1 Hi3 Hi5]") as
        "(Hi1 & Hi3 & Hi5 & Hi6 & Hx)"; [by iFrame|].
    rewrite later_exist. iDestruct "Hi6" as (u) "[Hi61 Hi62]".
    rewrite later_exist. iDestruct "Hi62" as (m) "[Hi62 [Hi63 Hi64]]".
    wp_load; iPvsIntro. iDestruct "Hi61" as %Hi61. iDestruct "Hi4" as %Hi4.
    iDestruct "Hi1" as %Hi1. iDestruct "Hi62" as %Hi62.
    iDestruct (graph_close with "[Hi3 Hi5 Hi63 Hi64 Hx]") as "(Hi1&Hi3&Hx)";
      eauto. iFrame. iExists _; eauto. iSplitR; eauto. by iExists _; iFrame.
    iSplitL "Hi1 Hi2 Hi3".
    { iNext. iApply Pack. iExists _, _; iFrame. by iSplitL; iPureIntro. }
    destruct u as [bu lu]; simpl. wp_focus (Fst _). iApply wp_fst; eauto.
    { by destruct lu as [[] []]; simpl; eauto. }
    iNext; iPvsIntro; wp_let. iInv graphN as "Hinv".
    clear Hi4 Hi1 Hi61.
    open_graph_inv "Hinv" "key" γ' mr' "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5)".
    iDestruct (graph_open_later with "[Hx Hi1 Hi3 Hi5]") as
        "(Hi1 & Hi3 & Hi5 & Hi6 & Hx)"; [by iFrame|].
    rewrite later_exist. iDestruct "Hi6" as (u) "[Hi61 Hi62]".
    rewrite later_exist. iDestruct "Hi62" as (m') "[Hi62 [Hi63 Hi64]]".
    iTimeless "Hi62". iDestruct "Hi62" as %Hi62'. rewrite Hi62' in Hi62.
    iTimeless "Hi61". iDestruct "Hi61" as %Hi61.
    iTimeless "Hi4". iDestruct "Hi4" as %Hi4.
    iTimeless "Hi1". iDestruct "Hi1" as %Hi1.
    inversion Hi62; subst; clear Hi62.
    destruct u as [[] lu']; simpl in *.
    - (* CAS fails *)
      wp_cas_fail.
      iDestruct (graph_close with "[Hi3 Hi5 Hi63 Hi64 Hx]") as "(Hi1&Hi3&Hx)";
      eauto. iFrame. iExists _; eauto. iSplitR; eauto. by iExists _; iFrame.
      iPvs (already_marked with "Hi2") as "[Hi2 Hxm]"; [|iFrame "Hxm"].
      { rewrite Hi4. eapply graph.is_marked; eauto. }
      iPvsIntro; iFrame. iNext; iApply Pack.
      unfold graph_inv; iExists _, _; iFrame; by repeat iSplitL.
    - (* CAS succeeds *)
      wp_cas_suc. rewrite (graph_expose_node g γ' x (false, lu')) //=.
      iDestruct (graph_pointsto_unmarked with "[Hi3 Hx]")
        as "[Hi3 [Hx %]]"; try by iFrame. by rewrite lookup_delete.
      subst.
      iPvs (mark_update_graph _ _ _ (Excl lu') with "[Hi3 Hx]") as "[Hi3 Hx]";
        try by iFrame. done. by rewrite lookup_delete.
      iPvs (new_marked with "Hi2") as "[Hi2 Hm]". iFrame "key Hm".
      erewrite mark_update_deleted.
      iDestruct (graph_close with "[Hi3 Hi5 Hi63 Hi64 Hx]") as "(Hi1&Hi3&Hx)";
        try iFrame.
      { by apply mark_update_dom_stable. }
      { iExists (_, _). iSplitR; [| iExists _; by iFrame].
          by rewrite mark_update_lookup. }
      iPvsIntro. iSplitR "Hx".
      + iNext; iApply Pack; unfold graph_inv. iExists _, _; iFrame.
        iSplit; iPureIntro.
        { by rewrite new_marking_dom marking_union Hi4. }
        { erewrite mark_update_dom_stable; eauto. }
      + iExists _; iFrame. iSplit; iPureIntro; eauto using unmarked_from_g.
  Qed.


End Helpers.