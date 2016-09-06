From iris.algebra Require Import frac dec_agree gmap upred_big_op.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre tactics.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Export lifting heap notation.
From iris.heap_lang.lib Require Import par.
From iris.program_logic Require Import cancelable_invariants.
Import uPred.

From iris_spanning_tree Require Import graph mon spanning.

Section wp_span.
  Context `{heapG Σ, cinvG Σ, authG Σ markingUR, authG Σ graphUR, spawnG Σ}.

  Lemma wp_span g markings (x : val) (l : loc) :
    l ∈ dom (gset _) g → maximal g → connected g l →
    heap_ctx ★
    ([★ map] l ↦ v ∈ g,
       ∃ (m : loc), markings !! l = Some m ★ l ↦ (#m, children_to_val v)
         ★ m ↦ #false) ⊢
      WP span (SOME #l)
      {{ _, ∃ g',
              ([★ map] l ↦ v ∈ g',
                ∃ m : loc, markings !! l = Some m ★ l ↦ (#m, children_to_val v)
                  ★ m ↦ #true)
             ★ dom (gset _) g = dom (gset _) g'
             ★ ■ strict_subgraph g g' ★ ■ tree g' l
      }}.
  Proof.
    iIntros (Hgl Hgmx Hgcn) "[#Hheap Hgr]".
    iVs (graph_ctx_alloc with "[Hgr]") as (Ig κ) "(key & #Hgr & Hg)";
      eauto.
    iApply wp_pvs.
    iApply wp_wand_l; iSplitR;
      [|iApply ((rec_wp_span κ g markings 1 1 (SOMEV #l)) with "[Hg key]");
        eauto; iFrame "#"; by iFrame].
    iIntros (v) "[H key]".
    unfold graph_ctx.
    iVs (cinv_cancel ⊤ graphN κ (graph_inv g markings) with "[#] [key]")
      as ">Hinv"; first done; try by iFrame.
    iClear "Hgr". unfold graph_inv.
    iDestruct "Hinv" as (G) "Hinv";
      iDestruct "Hinv" as (mr) "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5)".
    iDestruct "Hi4" as %Hi4. iDestruct "Hi5" as %Hi5.
    iDestruct "H" as "[H|H]".
    - iDestruct "H" as "(_ & H)". iDestruct "H" as (l') "(H1 & H2 & Hl')".
      iDestruct "H1" as %Hl; inversion Hl; subst.
      iDestruct "H2" as (G' gmr gtr) "(Hl1 & Hl2 & Hl3 & Hl4 & Hl5)".
      iDestruct "Hl2" as %Hl2. iDestruct "Hl3" as %Hl3. iDestruct "Hl4" as %Hl4.
      iDestruct (whole_frac with "[#]") as %Heq; [by iFrame|]; subst.
      iDestruct (marked_is_marked_in_auth_sepS with "[Hi2 Hl5]") as %Hmrk;
        [by iFrame|].
      iDestruct (own_graph_valid with "#Hl1") as %Hvl.
      iExists (Gmon_graph G').
      assert (dom (gset positive) g = dom (gset positive) (Gmon_graph G')).
      { erewrite front_t_t_dom; eauto.
        - by rewrite Gmon_graph_dom.
        - eapply front_mono; rewrite Gmon_graph_dom; eauto.
          by rewrite -Hi4. }
      iVsIntro. repeat iSplitL; try by iPureIntro.
      unfold heap_owns. rewrite of_graph_dom_eq //=.
      by rewrite big_sepM_fmap /=.
    - iDestruct "H" as "(_ & [H|H] & Hx)".
      + iDestruct "H" as %Heq. inversion Heq.
      + iDestruct "H" as (l') "(_ & Hl)".
        iDestruct (marked_is_marked_in_auth with "[Hi2 Hl]") as %Hmrk;
          [by iFrame|].
        iDestruct (whole_frac with "[#]") as %Heq; [by iFrame|]; subst.
        exfalso; revert Hmrk. rewrite Hi4 dom_empty. inversion 1.
  Qed.

End wp_span.