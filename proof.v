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

From iris_spanning_tree Require Import graph mon spanning.

Section wp_span.
  Context {Σ} {Ih : heapG Σ} {iSp : spawnG Σ}
          {IGm : authG heap_lang Σ markingUR} {IGi : inG heap_lang Σ invtokUR}
          {IGg : authG heap_lang Σ graphUR}.

  Local Opaque span.

  Lemma wp_span g Mrk (x : val) (l : loc) :
    marked g = ∅ →
    self_contained g l →
    connected g (λ m, true) l →
    (heap_ctx ★ ([★ map] l ↦ v ∈ g,
                 ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                              ★ m ↦ (ND_to_heap v).1))
      ⊢
      WP (span (SOME #l));; #()
      {{ _, ∃ g' (gtr : tree g' (λ _, true) l),
           ([★ map] l ↦ v ∈ g',
            ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                         ★ m ↦ (ND_to_heap v).1)
             (*★ ■ (graph_agrees g g') *)
      }}.
  Proof.
    iIntros (Hgnm Hgcn Hgsl) "[#Hheap Hgr]".
    iPvs (graph_ctx_alloc with "[Hgr]") as (Im Ig Ii) "(key & #Hgr & Hg)";
      eauto.
    wp_focus (span _).
    iApply wp_pvs.
    iApply wp_wand_l; iSplitR;
      [|iApply ((rec_wp_span _ _ _ _ (SOMEV #l)) with "[Hg key]"); eauto;
        iFrame "Hheap Hgr"; by iFrame].
    iIntros (v) "[H key]".
    unfold graph_ctx. iInv graphN as "Hinv".
    iDestruct (UnPack_later with "[Hinv key]") as "[Hinv key]";
      [iNext; iSplitL "key"; by iFrame|].
    iPvsIntro. iSplitL "key".
    { iNext. iApply (Dispose with "key"). }
    wp_seq. iPvsIntro.
    iDestruct "Hinv" as (γ) "Hinv";
      iDestruct "Hinv" as (mr) "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5 & Hi6)".
    iDestruct "Hi4" as %Hi4. iDestruct "Hi5" as %Hi5. iDestruct "Hi6" as %Hi6.
    iDestruct "H" as "[H|H]".
    - iDestruct "H" as "(_ & H)". iDestruct "H" as (l') "(H1 & H2 & Hl')".
      iDestruct "H1" as %Hl; inversion Hl; subst.
      iDestruct "H2" as (γ' gtr) "(Hl1 & Hl2 & Hl3)". iDestruct "Hl2" as %Hl2.
      iDestruct (whole_frac with "[Hi1 Hl1]") as "(Hi1 & Hl1 & %)";
        [by iFrame|]; subst.
      iDestruct (marked_is_marked_in_auth with "[Hi2 Hl3]") as %Hmrk;
        [by iFrame|].
      iDestruct (own_graph_valid with "Hl1") as "[Hl1 %]".
      iExists (of_graph g γ'). unshelve iExists _.
      { apply maximally_marked_tree_marked_dom_gives_tree; trivial.
        destruct gtr as [[? ?] ?].
        rewrite of_graph_dom; trivial.
        eapply (maximally_marked_dom_marked g); eauto.
        - (* use a lemma !*)
          admit.
        - by rewrite -{2}Hi4. }
      by iFrame.
  Admitted.

End wp_span.