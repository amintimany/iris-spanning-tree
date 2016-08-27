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

  Lemma wp_try_mark g Mrk k q (x : loc) :
    x ∈ dom (gset _) g →
    marked g = ∅ →
    (heap_ctx ★ graph_ctx g Mrk ★ Γρ(q, ∅) ★ κ(k))
      ⊢
      WP (try_mark #x)
      {{ v,
         (v = #true ★
               (∃ u, ((g !! x) = Some (false, u))
                       ★ Γρ(q, x [↦] u)) ★ μ(x) ★ κ(k))
           ∨ (v = #false ★ Γρ(q, ∅) ★ μ(x) ★ κ(k))
      }}.
  Proof.
    iIntros (Hgx Hgnm) "(#Hheap & #Hgr & Hx & key)". unfold try_mark.
    wp_let; wp_focus (! _)%E. unfold graph_ctx; iInv graphN as "Hinv".
    open_graph_inv "Hinv" "key" γ mr "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6)".
    iDestruct (@graph_open_later with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    rewrite later_exist. iDestruct "Hil" as (u) "[Hil1 Hil2]".
    rewrite later_exist. iDestruct "Hil2" as (m) "[Hil2 [Hil3 Hil4]]".
    wp_load; iPvsIntro. iDestruct "Hil1" as %Hil1. iDestruct "Hil2" as %Hil2.
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3";
      eauto. iFrame. iExists _; eauto. iSplitR; eauto. by iExists _; iFrame.
    iSplitL "Hi1 Hi2 Hi3 Hi5 Hi6 Hi4".
    { iNext. iApply Pack. iExists _, _; iFrame; auto. }
    destruct u as [bu lu]; simpl. wp_focus (Fst _). iApply wp_fst; eauto.
    { by destruct lu as [[] []]; simpl; eauto. }
    iNext; iPvsIntro; wp_let. iInv graphN as "Hinv".
    open_graph_inv "Hinv" "key" γ' mr' "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6)".
    iDestruct (graph_open_later with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    rewrite later_exist. iDestruct "Hil" as (u) "[Hil1 Hil2]".
    rewrite later_exist. iDestruct "Hil2" as (m') "[Hil2 [Hil3 Hil4]]".
    iTimeless "Hil2". iDestruct "Hil2" as %Hil2'.
    iTimeless "Hil1". iDestruct "Hil1" as %Hil1'.
    iTimeless "Hi5". iDestruct "Hi5" as %Hi5.
    iTimeless "Hi6". iDestruct "Hi6" as %Hi6.
    iTimeless "Hi4". iDestruct "Hi4" as %Hi4.
    rewrite Hil2' in Hil2; inversion Hil2; subst.
    destruct u as [[] lu']; simpl in *.
    - (* CAS fails *)
      wp_cas_fail.
      iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3";
        eauto. iFrame. iExists _; eauto. iSplitR; eauto. by iExists _; iFrame.
      iPvs (already_marked with "Hi2") as "[Hi2 Hxm]"; [|iFrame "Hxm"].
      { rewrite Hi4. eapply graph.is_marked; eauto. }
      iPvsIntro; iFrame. iSplitR "Hx".
      + iNext; iApply Pack.
        unfold graph_inv; iExists _, _; iFrame; repeat iSplitL; trivial.
      + by iRight; iFrame.
    - (* CAS succeeds *)
      wp_cas_suc.
      iDestruct (auth_own_graph_valid with "Hi1") as "[Hi1 H]".
      iDestruct "H" as %Hv1.
      iPvs (mark_graph _ _ x lu' with "[Hi1 Hx]") as "[Hi1 Hx]";
        try by iFrame. eapply unmarked_in_graph_mon; eauto.
      iPvs (new_marked with "Hi2") as "[Hi2 Hm]". iFrame "key Hm".
      erewrite delete_marked.
      iDestruct (auth_own_graph_valid with "Hi1") as "[Hi1 %]".
      iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3".
      { iFrame. iExists (_, _). iSplitR; [| iExists _; by iFrame].
          by rewrite mark_update_lookup. }
      pose proof (unmarked_from_g _ _ _ _ Hv1 Hil1') as Hfg.
      iPvsIntro. iSplitR "Hx".
      + iNext; iApply Pack; unfold graph_inv. iExists _, _; iFrame.
        repeat iSplit; iPureIntro.
        { by rewrite new_marking_dom marking_union //= Hi4. }
        { erewrite mark_dom_union => i. rewrite elem_of_union elem_of_singleton.
          intros [?|?]; subst; auto. }
        { apply agrees_op; trivial; split; eauto using nodes_agree_refl. }
      + iLeft; iSplit; trivial. iExists _; by iFrame.
  Qed.

  Lemma wp_unmark_fst g Mrk k q (x : loc) w1 w2 :
    (g !! x) = Some (false, (w1, w2)) →
    marked g = ∅ →
    (heap_ctx ★ graph_ctx g Mrk ★ Γρ(q, x [↦] (w1, w2)) ★ κ(k))
      ⊢
      WP (unmark_fst #x)
      {{ _, Γρ(q, x [↦] (None, w2)) ★ κ(k) }}.
  Proof.
    iIntros (Hgx Hgnm) "(#Hheap & #Hgr & Hx & key)". unfold unmark_fst.
    assert (Hgx' : x ∈ dom (gset _) g).
    { rewrite elem_of_dom Hgx; eauto. }
    wp_let; wp_focus (! _)%E. unfold graph_ctx; iInv graphN as "Hinv".
    open_graph_inv "Hinv" "key" γ mr "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6)".
    iDestruct (graph_open_later with "[Hi1 Hi3]")
      as "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    rewrite later_exist. iDestruct "Hil" as (u) "[Hil1 Hil2]".
    rewrite later_exist. iDestruct "Hil2" as (m) "[Hil2 [Hil3 Hil4]]".
    wp_load. iDestruct "Hi5" as %Hi5. iDestruct "Hil1" as %Hil1.
    iDestruct "Hil2" as %Hil2. iDestruct "Hi6" as %Hi6. iDestruct "Hi4" as %Hi4.
    iDestruct (auth_own_graph_valid with "Hi1") as "[Hi1 Hvγ]".
    iDestruct "Hvγ" as %Hvγ. iDestruct (graph_pointsto_marked with "[Hi1 Hx]")
      as "(Hi1 & Hx & Heq)"; try by iFrame.
    pose proof Hil1 as Hil1'. iDestruct "Heq" as %Heq; rewrite Heq in Hil1' Hvγ.
    rewrite mark_update_lookup in Hil1'; trivial.
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3"; [iFrame|].
    { iExists _; iSplitR; auto. iExists _; by iFrame. }
    iPvsIntro. iSplitL "Hi1 Hi2 Hi3".
    { iNext; iApply Pack. unfold graph_inv at 2.
      iExists _, _; iFrame; repeat iSplit; by iPureIntro. }
    clear Hil1 Hi6 Hi4 Hi5 Heq Hvγ. inversion Hil1'; subst. clear Hil1'.
    wp_let. wp_focus (Fst _). iApply wp_fst; eauto.
    { rewrite to_val_pr_opl_heap'; eauto. }
    iNext; iPvsIntro. wp_focus (Snd (_, _)). iApply wp_snd; eauto.
    { by rewrite to_val_pr_opl_heap'. }
    iNext; iPvsIntro. wp_focus (Snd _). iApply wp_snd; eauto.
    { rewrite to_val_opl_heap; eauto. }
    {by rewrite to_val_opl_heap. }
    iNext; iPvsIntro.
    iInv graphN as "Hinv".
    open_graph_inv "Hinv" "key" γ' mr' "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6)".
    iDestruct (graph_open_later with "[Hi1 Hi3]")
      as "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    rewrite later_exist. iDestruct "Hil" as (u) "[Hil1 Hil2]".
    rewrite later_exist. iDestruct "Hil2" as (m') "[Hil2 [Hil3 Hil4]]".
    wp_store.
    iDestruct "Hil2" as %Hil2'.
    rewrite Hil2' in Hil2. inversion Hil2; subst; clear Hil2.
    iDestruct "Hil1" as %Hil1. iDestruct "Hi4" as %Hi4. iDestruct "Hi5" as %Hi5.
    iDestruct "Hi6" as %Hi6.
    iDestruct (auth_own_graph_valid with "Hi1") as "[Hi1 Hvγ]".
    iDestruct "Hvγ" as %Hvγ. iDestruct (graph_pointsto_marked with "[Hi1 Hx]")
      as "(Hi1 & Hx & Heq)"; try by iFrame.
    pose proof Hil1 as Hil1'. iDestruct "Heq" as %Heq; rewrite Heq in Hil1' Hvγ.
    rewrite mark_update_lookup in Hil1'; trivial. inversion Hil1'; subst u.
    clear Hil1'. simpl. rewrite Heq.
    iPvs (update_graph _ _ _ (None, w2) with "[Hi1 Hx]") as
        "[Hi1 Hx]"; try by iFrame. by rewrite lookup_delete.
    rewrite -delete_marked. erewrite (delete_marked _ _ _ (None, w2)).
    assert (Hvγ' : ✓ ({[x := Excl (None, w2)]} ⋅ delete x γ')).
    { eapply updating_graph_valid; eauto. by rewrite lookup_delete. }
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3".
    { iFrame. iExists _. iSplitR.
      - rewrite ?mark_update_lookup; eauto. - iExists _; by iFrame. }
    iPvsIntro; iFrame.
    iNext. iApply Pack. unfold graph_inv at 2.
    iExists _, _; iFrame. repeat iSplit; iPureIntro.
    { rewrite Heq in Hi4. rewrite Hi4 ?marking_union; trivial. }
    { rewrite mark_dom_union => i.
      rewrite elem_of_union dom_delete elem_of_singleton.
      intros [->|Hdf]; trivial. apply elem_of_difference in Hdf.
      apply Hi5; tauto. }
    { apply agrees_op; trivial. split; [by apply agrees_deleted|].
      eexists; split; eauto. destruct w2; done. }
  Qed.

  Lemma wp_unmark_snd g Mrk k q (x : loc) w1 w2 :
    (g !! x) = Some (false, (w1, w2)) →
    marked g = ∅ →
    (heap_ctx ★ graph_ctx g Mrk ★ Γρ(q, x [↦] (w1, w2)) ★ κ(k))
      ⊢
      WP (unmark_snd #x)
      {{ _, Γρ(q, x [↦] (w1, None)) ★ κ(k) }}.
  Proof.
    iIntros (Hgx Hgnm) "(#Hheap & #Hgr & Hx & key)". unfold unmark_fst.
    assert (Hgx' : x ∈ dom (gset _) g).
    { rewrite elem_of_dom Hgx; eauto. }
    wp_let; wp_focus (! _)%E. unfold graph_ctx; iInv graphN as "Hinv".
    open_graph_inv "Hinv" "key" γ mr "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6)".
    iDestruct (graph_open_later with "[Hi1 Hi3]")
      as "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    rewrite later_exist. iDestruct "Hil" as (u) "[Hil1 Hil2]".
    rewrite later_exist. iDestruct "Hil2" as (m) "[Hil2 [Hil3 Hil4]]".
    wp_load. iDestruct "Hi5" as %Hi5. iDestruct "Hil1" as %Hil1.
    iDestruct "Hil2" as %Hil2. iDestruct "Hi6" as %Hi6. iDestruct "Hi4" as %Hi4.
    iDestruct (auth_own_graph_valid with "Hi1") as "[Hi1 Hvγ]".
    iDestruct "Hvγ" as %Hvγ. iDestruct (graph_pointsto_marked with "[Hi1 Hx]")
      as "(Hi1 & Hx & Heq)"; try by iFrame.
    pose proof Hil1 as Hil1'. iDestruct "Heq" as %Heq; rewrite Heq in Hil1' Hvγ.
    rewrite mark_update_lookup in Hil1'; trivial.
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3"; [iFrame|].
    { iExists _; iSplitR; auto. iExists _; by iFrame. }
    iPvsIntro. iSplitL "Hi1 Hi2 Hi3".
    { iNext; iApply Pack. unfold graph_inv at 2.
      iExists _, _; iFrame; repeat iSplit; by iPureIntro. }
    clear Hil1 Hi6 Hi4 Hi5 Heq Hvγ. inversion Hil1'; subst. clear Hil1'.
    wp_let. wp_focus (Fst _). iApply wp_fst; eauto.
    { rewrite to_val_pr_opl_heap'; eauto. }
    iNext; iPvsIntro. wp_focus (Snd (_, _)). iApply wp_snd; eauto.
    { by rewrite to_val_pr_opl_heap'. }
    iNext; iPvsIntro. wp_focus (Fst _). iApply wp_fst; eauto.
    {by rewrite to_val_opl_heap. }
    { rewrite to_val_opl_heap; eauto. }
    iNext; iPvsIntro.
    iInv graphN as "Hinv".
    open_graph_inv "Hinv" "key" γ' mr' "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6)".
    iDestruct (graph_open_later with "[Hi1 Hi3]")
      as "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    rewrite later_exist. iDestruct "Hil" as (u) "[Hil1 Hil2]".
    rewrite later_exist. iDestruct "Hil2" as (m') "[Hil2 [Hil3 Hil4]]".
    wp_store.
    iDestruct "Hil2" as %Hil2'.
    rewrite Hil2' in Hil2. inversion Hil2; subst; clear Hil2.
    iDestruct "Hil1" as %Hil1. iDestruct "Hi4" as %Hi4. iDestruct "Hi5" as %Hi5.
    iDestruct "Hi6" as %Hi6.
    iDestruct (auth_own_graph_valid with "Hi1") as "[Hi1 Hvγ]".
    iDestruct "Hvγ" as %Hvγ. iDestruct (graph_pointsto_marked with "[Hi1 Hx]")
      as "(Hi1 & Hx & Heq)"; try by iFrame.
    pose proof Hil1 as Hil1'. iDestruct "Heq" as %Heq; rewrite Heq in Hil1' Hvγ.
    rewrite mark_update_lookup in Hil1'; trivial. inversion Hil1'; subst u.
    clear Hil1'. simpl. rewrite Heq.
    iPvs (update_graph _ _ _ (w1, None) with "[Hi1 Hx]") as
        "[Hi1 Hx]"; try by iFrame. by rewrite lookup_delete.
    rewrite -delete_marked. erewrite (delete_marked _ _ _ (w1, None)).
    assert (Hvγ' : ✓ ({[x := Excl (w1, None)]} ⋅ delete x γ')).
    { eapply updating_graph_valid; eauto. by rewrite lookup_delete. }
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3".
    { iFrame. iExists _. iSplitR.
      - rewrite ?mark_update_lookup; eauto. - iExists _; by iFrame. }
    iPvsIntro; iFrame.
    iNext. iApply Pack. unfold graph_inv at 2.
    iExists _, _; iFrame. repeat iSplit; iPureIntro.
    { rewrite Heq in Hi4. rewrite Hi4 ?marking_union; trivial. }
    { rewrite mark_dom_union => i.
      rewrite elem_of_union dom_delete elem_of_singleton.
      intros [->|Hdf]; trivial. apply elem_of_difference in Hdf.
      apply Hi5; tauto. }
    { apply agrees_op; trivial. split; [by apply agrees_deleted|].
      eexists; split; eauto. destruct w1; done. }
  Qed.
(*
  Lemma rec_wp_span g Mrk k q (x : val) γ :
    marked (of_base_graph g γ) = ∅ →
    marked g = ∅ →
    (x = NONEV ∨ ∃ l : loc, x = SOMEV #l ∧ l ∈ dom (gset positive) γ) →
    (heap_ctx ★ graph_ctx g Mrk ★ Γρ(q, γ) ★ κ(k))
      ⊢
      WP (span x)
      {{ v,
         (v = # true ∧
          ∃ l : loc,
            x = SOMEV #l ∧
            (∃ γ' (mmr : (maximal_marked_tree (of_base_graph g γ') l)),
                Γρ(q, γ') ★
                  ([★ set] l ∈
                           (front
                              (of_base_graph g γ')
                              (marked (of_base_graph g γ'))) , μ(l))
            ) ★ μ(l) ★ κ(k)
          )
         ∨
         (v = # false ∧ x = NONEV ∧ Γρ(q, γ) ★ κ(k))
      }}.
  Proof.
    intros Hunm Hgnm Hx. iIntros "(#Hheap & #Hgr & Hx & key)".
    iRevert (q) "Hx". iLöb as "IH". iIntros (q) "Hx".
    wp_rec. destruct Hx as [|[l [? Hlid]]]; subst.
    { wp_match. iPvsIntro. iRight; repeat iSplit; trivial; by iFrame. }
    wp_match. erewrite (own_graph_get_singleton _ _ _ l); eauto.
*)








    
    
End Helpers.