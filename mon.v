From iris.heap_lang Require Export lifting heap notation.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre ghost_ownership
     tactics invariants.
Import uPred.

From iris.program_logic Require Import cancelable_invariants.

From iris.algebra Require Import base cmra gmap.
From iris.prelude Require Import gmap mapset.

Require Import iris_spanning_tree.graph.

(* children cofe *)
Canonical Structure chlC := leibnizC (option loc * option loc)%type.
(* The graph monoid. *)
Definition graphN : namespace := nroot .@ "SPT_graph".
Definition graphUR : ucmraT :=
  optionUR (prodR fracR (gmapR loc (exclR chlC))).
(* The monoid for talking about which nodes are marked.
These markings are duplicatable. *)
Definition markingUR : ucmraT := gmapUR loc unitR.

(** The CMRA we need. *)
Class graphG Σ := GraphG
  {
    graph_marking_inG :> authG Σ markingUR;
    graph_marking_name : gname;
    graph_inG :> authG Σ graphUR;
    graph_name : gname
  }.
(** The Functor we need. *)
(*Definition graphΣ : gFunctors := #[authΣ graphUR].*)

Section marking_definitions.
  Context `{irisG heap_lang Σ, graphG Σ}.

  Definition is_marked (l : loc) : iProp Σ :=
    auth_own graph_marking_name ({[ l := () ]} : markingUR).

  Lemma dup_marking (m : markingUR) : m ≡ m ⋅ m.
  Proof.
    intros i. rewrite lookup_op.
    match goal with
      |- ?B ≡ ?A ⋅ ?A => change B with A; by destruct A as [[]|]
    end.
  Qed.

  Global Instance marked_persistentP x : PersistentP (is_marked x).
  Proof. apply _. Qed.

  Lemma dup_marked l : is_marked l ⊣⊢ is_marked l ★ is_marked l.
  Proof. by rewrite /is_marked -auth_own_op -dup_marking. Qed.

  Lemma new_marked_local_update (m m' : markingUR) : ∅ ~l~> m' @ Some m.
  Proof.
    constructor.
    - intros ? ? i. rewrite //= lookup_op.
      case _ : (m !! i) => [[]|]; case _ : (m' !! i) => [[]|] //=.
    - intros ? [?|]; rewrite //= ?left_id => ? -> //; rewrite right_id //.
  Qed.

  Lemma new_marked_update {m : markingUR} l :
    (● m ⋅ ◯ ∅) ~~> (● (m ⋅ {[l := () ]}) ⋅ ◯ ({[l := () ]})).
  Proof.
    rewrite -{1}(ucmra_unit_left_id m) (comm op m).
    apply auth_update, new_marked_local_update.
  Qed.

  Lemma new_marked {E} (m : markingUR) l :
  own graph_marking_name (● m) ={E}=>
  own graph_marking_name (● (m ⋅ {[l := () ]})) ★ is_marked l.
  Proof.
    iIntros "H1".
    iVs (auth_empty (A := markingUR) graph_marking_name) as "H2".
    unfold auth_own; iCombine "H1" "H2" as "H".
    iVs (@own_update with "[H]") as "Y"; eauto using new_marked_update.
    by rewrite /is_marked /auth_own own_op.
  Qed.

  Lemma already_marked_op (m : markingUR) l :
    l ∈ dom (gset _) m → m = m ⋅ {[l := () ]}.
  Proof.
    rewrite elem_of_dom. intros [[] Hz]; apply: map_eq => i.
    destruct (decide (i = l)); subst;
      rewrite ?lookup_op ?Hz ?lookup_singleton
        ?lookup_singleton_ne //=; rewrite right_id_L //.
  Qed.

  Lemma already_marked {E} (m : markingUR) l : l ∈ dom (gset _) m →
    own graph_marking_name (● m) ={E}=>
    own graph_marking_name (● m) ★ is_marked l.
  Proof.
    iIntros (Hl) "Hm". iVs (new_marked with "Hm") as "[H1 H2]"; iFrame.
    by rewrite -already_marked_op.
  Qed.

End marking_definitions.

(* The monoid representing graphs *)
Definition Gmon := gmapR loc (exclR chlC).

Definition excl_chlC_chl (ch : exclR chlC) : option (option loc * option loc) :=
  match ch with
  | Excl w => Some w
  | Excl_Bot => None
  end.

Definition Gmon_graph (G : Gmon) : graph loc := omap excl_chlC_chl G.

Definition Gmon_graph_dom (G : Gmon) :
  ✓ G → dom (gset _) (Gmon_graph G) = dom (gset _) G.
Proof.
  intros Hvl; apply mapset_eq => i. rewrite ?elem_of_dom lookup_omap.
  specialize (Hvl i). split.
  - revert Hvl; case _ : (G !! i) => [[]|] //=; eauto.
    intros _ [? Hgi]; inversion Hgi.
  - intros Hgi; revert Hgi Hvl. intros [[] Hgi]; rewrite Hgi; inversion 1; eauto.
Qed.

Definition child_to_val (c : option loc) : val :=
  match c with
  | None => NONEV
  | Some l => SOMEV #l
  end.

(* convert the data of a node to a value in the heap *)
Definition children_to_val (ch : option loc * option loc) : val :=
  (child_to_val (ch.1), child_to_val (ch.2)).

Lemma children_to_val_is_val (c c' : option loc) :
  to_val (child_to_val c, child_to_val c') =
  Some (child_to_val c, child_to_val c')%V.
Proof. by destruct c; destruct c'. Qed.

Definition marked_graph := gmap loc (bool * (option loc * option loc)).
Identity Coercion marked_graph_gmap: marked_graph >-> gmap.

Definition of_graph_elem (G : Gmon) i v
  : option (bool * (option loc * option loc)) :=
  match Gmon_graph G !! i with
  | Some w => Some (true, w)
  | None => Some (false,v)
  end.

Definition of_graph (g : graph loc) (G : Gmon) : marked_graph :=
  map_imap (of_graph_elem G) g.

(* facts *)

Global Instance Gmon_graph_proper : Proper ((≡) ==> (=)) Gmon_graph.
Proof. solve_proper. Qed.

Lemma new_Gmon_dom (G : Gmon) x w :
  dom (gset loc) (G ⋅ {[x := w]}) = dom (gset loc) G ∪ {[x]}.
Proof. by rewrite dom_op dom_singleton_L. Qed.

Definition of_graph_empty (g : graph loc) :
  of_graph g ∅ = fmap (λ x, (false, x)) g.
Proof.
  apply: map_eq => i.
  rewrite lookup_imap /of_graph_elem lookup_fmap lookup_omap //.
Qed.

Section definitions.
  Context `{heapG Σ, graphG Σ}.

  Definition own_graph (q : frac) (G : Gmon) : iProp Σ :=
    own graph_name (◯ (Some (q, G) : graphUR)).

  Global Instance own_graph_proper q : Proper ((≡) ==> (⊣⊢)) (own_graph q).
  Proof. solve_proper. Qed.

  Definition heap_owns (M : marked_graph) (markings : gmap loc loc) : iProp Σ :=
    ([★ map] l ↦ v ∈ M, ∃ (m : loc), markings !! l = Some m
       ★ l ↦ (#m, children_to_val (v.2)) ★ m ↦ #(v.1))%I.

  Definition graph_inv (g : graph loc) (markings : gmap loc loc) : iProp Σ :=
    (∃ (G : Gmon) (M : markingUR),
       own graph_name (● Some (1%Qp, G)) ★ own graph_marking_name (● M)
       ★ heap_owns (of_graph g G) markings
       ★ dom (gset _) M = dom (gset _) G ★ ■ (strict_subgraph g (Gmon_graph G))
    )%I.

  Global Instance graph_inv_timeless g Mrk : TimelessP (graph_inv g Mrk).
  Proof. apply _. Qed.

  Context `{cinvG Σ}.
  Definition graph_ctx κ g Mrk : iProp Σ := cinv graphN κ (graph_inv g Mrk).

  Global Instance graph_ctx_persistent κ g Mrk : PersistentP (graph_ctx κ g Mrk).
  Proof. apply _. Qed.

End definitions.

Notation "l [↦] v" := ({[l := Excl v]}) (at level 70, format "l  [↦]  v").

Typeclasses Opaque graph_ctx graph_inv own_graph.

Section graph_ctx_alloc.
  Context `{heapG Σ, cinvG Σ, authG Σ markingUR, authG Σ graphUR}.

  Lemma graph_ctx_alloc (E : coPset) (g : graph loc) (markings : gmap loc loc)
        (HNE : (nclose graphN) ⊆ E)
  : ([★ map] l ↦ v ∈ g, ∃ (m : loc), markings !! l = Some m
       ★ l ↦ (#m, children_to_val v) ★ m ↦ #false)
     ={E}=> ∃ (Ig : graphG Σ) (κ : gname), cinv_own κ 1 ★ graph_ctx κ g markings
             ★ own_graph 1%Qp ∅.
  Proof.
    iIntros "H1".
    iVs (own_alloc (● (∅ : markingUR))) as (mn) "H2"; first done.
    iVs (own_alloc (● (Some (1%Qp, ∅ : Gmon) : graphUR)
                      ⋅ ◯ (Some (1%Qp, ∅ : Gmon) : graphUR))) as (gn) "H3".
    { done. }
    iDestruct "H3" as "[H31 H32]".
    set (Ig := GraphG _ _ mn _ gn).
    iExists Ig.
    iAssert (graph_inv g markings) with "[H1 H2 H31]" as "H".
    { unfold graph_inv. iExists ∅, ∅.
      iFrame "H2 H31".
      iSplitL; [|iSplit; iPureIntro].
      - rewrite /heap_owns of_graph_empty  big_sepM_fmap; eauto.
      - by rewrite ?dom_empty_L.
      - rewrite /Gmon_graph omap_empty; apply strict_subgraph_empty. }
    iVs (cinv_alloc _ graphN with "[H]") as (κ) "[Hinv key]".
    { iNext. iExact "H". }
    iExists κ.
    rewrite /own_graph /graph_ctx //=; by iFrame.
  Qed.

End graph_ctx_alloc.

Lemma marked_was_unmarked (G : Gmon) x v :
  ✓ ({[x := Excl v]} ⋅ G) → G !! x = None.
Proof.
  intros H2; specialize (H2 x).
  revert H2; rewrite lookup_op lookup_singleton. intros H2.
    by rewrite (excl_validN_inv_l O _ _ (proj1 (cmra_valid_validN _) H2 O)).
Qed.

Lemma mark_update_lookup_base (G : Gmon) x v :
  ✓ ({[x := Excl v]} ⋅ G) → ({[x := Excl v]} ⋅ G) !! x = Some (Excl v).
Proof.
  intros H2; rewrite lookup_op lookup_singleton.
  erewrite marked_was_unmarked; eauto.
Qed.

Lemma mark_update_lookup_ne_base (G : Gmon) x i v :
  i ≠ x → ({[x := Excl v]} ⋅ G) !! i = G !! i.
Proof. intros H. by rewrite lookup_op lookup_singleton_ne //= left_id_L. Qed.

Lemma of_graph_dom g G : dom (gset _) (of_graph g G) = dom (gset _) g.
Proof.
  apply mapset_eq=>i.
  rewrite ?elem_of_dom lookup_imap /of_graph_elem lookup_omap.
  case _ : (g !! i) => [x|]; case _ : (G !! i) => [[]|] //=; split;
  intros [? Hcn]; inversion Hcn; eauto.
Qed.

Lemma in_dom_of_graph (g : graph loc) (G : Gmon) x (b : bool) v :
  ✓ G → of_graph g G !! x = Some (b, v) → b ↔ x ∈ dom (gset _) G.
Proof.
  rewrite /of_graph /of_graph_elem lookup_imap lookup_omap elem_of_dom.
  intros Hvl; specialize (Hvl x); revert Hvl;
  case _ : (g !! x) => [?|]; case _ : (G !! x) => [[] ?|] //=;
    intros Hvl; inversion Hvl; try (inversion 1; subst); split;
    try (inversion 1; fail); try (intros [? Hcn]; inversion Hcn; fail);
    subst; eauto.
Qed.

Global Instance of_graph_proper g : Proper ((≡) ==> (=)) (of_graph g).
Proof. solve_proper. Qed.


Lemma mark_update_lookup (g : graph loc) (G : Gmon) x v :
  x ∈ dom (gset _) g →
  ✓ ((x [↦] v) ⋅ G) → of_graph g ((x [↦] v) ⋅ G) !! x = Some (true, v).
Proof.
  rewrite elem_of_dom /is_Some. intros [w H1] H2.
  rewrite /of_graph /of_graph_elem lookup_imap H1 lookup_omap; simpl.
  rewrite mark_update_lookup_base; trivial.
Qed.

Lemma mark_update_lookup_ne (g : graph loc) (G : Gmon) x i v :
  i ≠ x → of_graph g ((x [↦] v) ⋅ G) !! i = (of_graph g G) !! i.
Proof.
  intros H. rewrite /of_graph /of_graph_elem ?lookup_imap ?lookup_omap; simpl.
  rewrite mark_update_lookup_ne_base //=.
Qed.

Section graph.
  Context `{heapG Σ, graphG Σ}.

  Lemma own_graph_valid q G : own_graph q G ⊢ ✓ G.
  Proof.
    iIntros "H". unfold own_graph.
    by iDestruct (own_valid with "#H") as %[_ ?].
  Qed.

  Lemma auth_own_graph_valid q G : own graph_name (● Some (q, G))  ⊢ ✓ G.
  Proof.
    iIntros "H". unfold own_graph.
    by iDestruct (own_valid with "#H") as %[_ [_ ?]].
  Qed.

  Lemma whole_frac (G G' : Gmon):
    own graph_name (● Some (1%Qp, G)) ★ own_graph 1 G' ⊢ G = G'.
  Proof.
    iIntros "[H1 H2]". rewrite /own_graph.
    iCombine "H1" "H2" as "H".
    iDestruct (own_valid with "#H") as %[H1 H2]; cbn in *.
    iPureIntro. apply: map_eq => i. admit.
  Admitted.

  Lemma graph_divide q G G' :
    own_graph q (G ⋅ G') ⊣⊢ own_graph (q / 2) G ★ own_graph (q / 2) G'.
  Proof.
    replace q with ((q / 2) + (q / 2))%Qp at 1 by (by rewrite Qp_div_2).
      by rewrite /own_graph -auth_own_op.
  Qed.

  Lemma mark_graph {E} (G : Gmon) q x w : G !! x = None →
    own graph_name (● Some (1%Qp, G)) ★ own_graph q ∅
    ={E}=>
    own graph_name (● Some (1%Qp, {[x := Excl w]} ⋅ G)) ★ own_graph q (x [↦] w).
  Proof.
    iIntros (Hx) "H". rewrite -?own_op.
    iVs (own_update with "H") as "H'"; eauto.
  Admitted.

  Lemma update_graph {E} (G : Gmon) q x w m :
    G !! x = None →
    own graph_name (● Some (1%Qp, {[x := Excl m]} ⋅ G))
       ★ own_graph q (x [↦] m)
      ⊢ |={E}=> own graph_name (● Some (1%Qp, {[x := Excl w]} ⋅ G))
                  ★ own_graph q (x [↦] w).
  Proof.
    iIntros (Hx) "H". rewrite -?own_op.
    iVs (own_update with "H") as "H'"; eauto.
  Admitted.

  Lemma graph_pointsto_marked (G : Gmon) q x w :
    own graph_name (● Some (1%Qp, G)) ★ own_graph q (x [↦] w)
      ⊢ G = {[x := Excl w]} ⋅ (delete x G).
  Proof.
    rewrite /own_graph -?own_op. iIntros "H".
    iDestruct (@own_valid with "#H") as %[H1 H2]; simpl in *.
    iPureIntro.
  Admitted.

  Lemma graph_open (g :graph loc) (markings : gmap loc loc) (G : Gmon) x
  : x ∈ dom (gset _) g →
    own graph_name (● Some (1%Qp, G)) ★ heap_owns (of_graph g G) markings ⊢
    own graph_name (● Some (1%Qp, G))
    ★ heap_owns (delete x (of_graph g G)) markings
    ★ (∃ u : bool * (option loc * option loc), (of_graph g G !! x = Some u)
         ★ ∃ (m : loc), markings !! x = Some m ★ x ↦ (#m, children_to_val (u.2))
           ★ m ↦ #(u.1)).
  Proof.
    iIntros (Hx) "(Hg & Ha)".
    assert (Hid : x ∈ dom (gset _) (of_graph g G)) by (by rewrite of_graph_dom).
    revert Hid; rewrite elem_of_dom /is_Some. intros [y Hy].
    rewrite /heap_owns -{1}(insert_id _ _ _ Hy) -insert_delete.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
    iDestruct "Ha" as "[H $]". iFrame "Hg". iExists _; eauto.
  Qed.

  Lemma graph_close g markings G x :
    heap_owns (delete x (of_graph g G)) markings
    ★ (∃ u : bool * (option loc * option loc), (of_graph g G !! x = Some u)
        ★ ∃ (m : loc), markings !! x = Some m ★ x ↦ (#m, children_to_val (u.2))
            ★ m ↦ #(u.1))
    ⊢ heap_owns (of_graph g G) markings.
  Proof.
    iIntros "[Ha Hl]". iDestruct "Hl" as (u) "[Hu Hl]". iDestruct "Hu" as %Hu.
    rewrite /heap_owns -{2}(insert_id _ _ _ Hu) -insert_delete.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto]. by iFrame "Ha".
  Qed.

  Lemma marked_is_marked_in_auth (mr : markingUR) l :
    own graph_marking_name (● mr) ★ is_marked l ⊢ ■ (l ∈ dom (gset _) mr).
  Proof.
    iIntros "H". unfold is_marked. rewrite -own_op.
    iDestruct (own_valid with "#H") as %Hvl.
    iPureIntro. rewrite elem_of_dom.
    destruct Hvl as [Hvl _]; simpl in *.
    destruct (Hvl O) as [z Hvl']. specialize (Hvl' l).
    inversion Hvl' as [? ? ? Hvl1 Hvl2|Hvl1 Hvl2]; [rewrite -Hvl1; eauto|].
    revert Hvl2. rewrite ?lookup_op lookup_empty lookup_singleton.
    case _ : (z !! l); inversion 1.
  Qed.

  Lemma marked_is_marked_in_auth_sepS (mr : markingUR) m :
    own graph_marking_name (● mr) ★ ([★ set] l ∈ m, is_marked l)
        ⊢ ■ (m ⊆ dom (gset _) mr).
  Proof.
    iIntros "[Hmr Hm]". rewrite big_sepS_forall pure_forall.
    iIntros (x). rewrite pure_impl. iIntros (Hx).
    iApply marked_is_marked_in_auth.
    iFrame. by iApply "Hm".
  Qed.

End graph.

(* Graph properties *)

Lemma delete_marked g G x w :
  delete x (of_graph g G) = delete x (of_graph g ((x [↦] w) ⋅ G)).
Proof.
  apply: map_eq => i. destruct (decide (i = x)).
  - subst; by rewrite ?lookup_delete.
  - rewrite ?lookup_delete_ne //= /of_graph /of_graph_elem ?lookup_imap
      ?lookup_omap; case _ : (g !! i) => [v|] //=.
    by rewrite lookup_op lookup_singleton_ne //= left_id_L.
Qed.

Lemma in_dom_conv (G G' : Gmon) x : ✓ (G ⋅ G') → x ∈ dom (gset _) (Gmon_graph G)
  → (Gmon_graph (G ⋅ G')) !! x = (Gmon_graph G) !! x.
Proof.
  intros HGG. specialize (HGG x). revert HGG.
  rewrite /get_left /Gmon_graph elem_of_dom /is_Some ?lookup_omap lookup_op.
  case _ : (G !! x) => [[]|]; case _ : (G' !! x) => [[]|]; do 2 inversion 1;
    simpl in *; auto; congruence.
Qed.
Lemma in_dom_conv' (G G' : Gmon) x: ✓(G ⋅ G') → x ∈ dom (gset _) (Gmon_graph G')
  → (Gmon_graph (G ⋅ G')) !! x = (Gmon_graph G') !! x.
Proof. rewrite comm; apply in_dom_conv. Qed.
Lemma get_left_conv (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (gset _) (Gmon_graph G) → get_left (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_left (Gmon_graph G) x = Some xl.
Proof. intros. rewrite /get_left in_dom_conv; auto. Qed.
Lemma get_left_conv' (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (gset _) (Gmon_graph G') → get_left (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_left (Gmon_graph G') x = Some xl.
Proof. rewrite comm; apply get_left_conv. Qed.
Lemma get_right_conv (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (gset _) (Gmon_graph G) → get_right (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_right (Gmon_graph G) x = Some xl.
Proof. intros. rewrite /get_right in_dom_conv; auto. Qed.
Lemma get_right_conv' (G G' : Gmon) x xl : ✓ (G ⋅ G') →
  x ∈ dom (gset _) (Gmon_graph G') → get_right (Gmon_graph (G ⋅ G')) x = Some xl
  ↔ get_right (Gmon_graph G') x = Some xl.
Proof. rewrite comm; apply get_right_conv. Qed.

Lemma in_op_dom (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom (gset loc) (Gmon_graph G) → y ∈ dom (gset loc) (Gmon_graph (G ⋅ G')).
Proof. refine (λ H x, _ x); rewrite ?elem_of_dom ?in_dom_conv ; eauto. Qed.
Lemma in_op_dom' (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom (gset loc) (Gmon_graph G') → y ∈ dom (gset loc) (Gmon_graph (G ⋅ G')).
Proof. rewrite comm; apply in_op_dom. Qed.

Local Hint Resolve cmra_valid_op_l cmra_valid_op_r in_op_dom in_op_dom'.

Lemma in_op_dom_alt (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom (gset loc) G → y ∈ dom (gset loc) (G ⋅ G').
Proof. intros HGG; rewrite -?Gmon_graph_dom; eauto. Qed.
Lemma in_op_dom_alt' (G G' : Gmon) y : ✓(G ⋅ G') →
  y ∈ dom (gset loc) G' → y ∈ dom (gset loc) (G ⋅ G').
Proof. intros HGG; rewrite -?Gmon_graph_dom; eauto. Qed.

Local Hint Resolve in_op_dom_alt in_op_dom_alt'.
Local Hint Extern 1 => eapply get_left_conv + eapply get_left_conv' +
  eapply get_right_conv + eapply get_right_conv'.

Local Hint Extern 1 (_ ∈ dom (gset loc) (Gmon_graph _)) =>
  erewrite Gmon_graph_dom.

Local Hint Resolve path_start path_end.

Lemma path_conv (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → maximal (Gmon_graph G) → x ∈ dom (gset _) G →
  valid_path (Gmon_graph (G ⋅ G')) x y p → valid_path (Gmon_graph G) x y p.
Proof.
  intros Hv Hm. rewrite -Gmon_graph_dom //=; eauto. revert x y.
  induction p as [|[] p]; inversion 2; subst; econstructor; eauto;
    try eapply IHp; try eapply Hm; eauto.
Qed.
Lemma path_conv_back (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → x ∈ dom (gset _) G →
  valid_path (Gmon_graph G) x y p → valid_path (Gmon_graph (G ⋅ G')) x y p.
Proof.
  intros Hv. rewrite -Gmon_graph_dom //=; eauto. revert x y.
  induction p as [|[] p]; inversion 2; subst; econstructor; eauto;
    try eapply IHp; eauto.
Qed.
Lemma path_conv' (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → maximal (Gmon_graph G') → x ∈ dom (gset _) G' →
  valid_path (Gmon_graph (G ⋅ G')) x y p → valid_path (Gmon_graph G') x y p.
Proof. rewrite comm; eapply path_conv. Qed.
Lemma path_conv_back' (G G' : Gmon) x y p :
  ✓ (G ⋅ G') → x ∈ dom (gset _) G' →
  valid_path (Gmon_graph G') x y p → valid_path (Gmon_graph (G ⋅ G')) x y p.
Proof. rewrite comm; apply path_conv_back. Qed.

Local Ltac in_dom_Gmon_graph :=
  rewrite Gmon_graph_dom //= ?dom_op ?elem_of_union ?dom_singleton
      ?elem_of_singleton.

Lemma get_left_singleton x vl vr :
  get_left (Gmon_graph (x [↦] (vl, vr))) x = vl.
Proof. rewrite /get_left /Gmon_graph lookup_omap lookup_singleton; done. Qed.
Lemma get_right_singleton x vl vr :
  get_right (Gmon_graph (x [↦] (vl, vr))) x = vr.
Proof. rewrite /get_right /Gmon_graph lookup_omap lookup_singleton; done. Qed.

Lemma graph_in_dom_op (G G' : Gmon) x :
  ✓ (G ⋅ G') → x ∈ dom (gset _) G → x ∉ dom (gset _) G'.
Proof.
  intros HGG. specialize (HGG x). revert HGG. rewrite ?elem_of_dom lookup_op.
  case _ : (G !! x) => [[]|]; case _ : (G' !! x) => [[]|]; inversion 1;
  do 2 (intros [? Heq]; inversion Heq; clear Heq).
Qed.
Lemma graph_in_dom_op' (G G' : Gmon) x :
  ✓ (G ⋅ G') → x ∈ dom (gset _) G' → x ∉ dom (gset _) G.
Proof. rewrite comm; apply graph_in_dom_op. Qed.
Lemma graph_op_path (G G' : Gmon) x z p :
  ✓ (G ⋅ G') → x ∈ dom (gset _) G → valid_path (Gmon_graph G') z x p → False.
Proof.
  intros ?? Hp%path_end; rewrite Gmon_graph_dom in Hp; eauto.
  eapply graph_in_dom_op; eauto.
Qed.
Lemma graph_op_path' (G G' : Gmon) x z p :
  ✓ (G ⋅ G') → x ∈ dom (gset _) G' → valid_path (Gmon_graph G) z x p → False.
Proof. rewrite comm; apply graph_op_path. Qed.

Lemma in_dom_singleton (x : loc) (w : chlC) : x ∈ dom (gset _) (x [↦] w).
Proof. by rewrite dom_singleton elem_of_singleton. Qed.


Local Hint Resolve graph_op_path graph_op_path' in_dom_singleton.

Lemma maximal_op (G G' : Gmon) : ✓ (G ⋅ G') → maximal (Gmon_graph G)
  → maximal (Gmon_graph G') → maximal (Gmon_graph (G ⋅ G')).
Proof.
  intros Hvl [_ HG] [_ HG']. split; trivial => x v.
  rewrite Gmon_graph_dom ?dom_op ?elem_of_union -?Gmon_graph_dom; eauto.
  intros [Hxl|Hxr].
  - erewrite get_left_conv, get_right_conv; eauto.
  - erewrite get_left_conv', get_right_conv'; eauto.
Qed.

Lemma maximal_op_singleton (G : Gmon) x vl vr :
  ✓ ((x [↦] (vl, vr)) ⋅ G) → maximal(Gmon_graph G) →
  match vl with | Some xl => xl ∈ dom (gset _) G | None => True end →
  match vr with | Some xr => xr ∈ dom (gset _) G | None => True end →
  maximal (Gmon_graph ((x [↦] (vl, vr)) ⋅ G)).
Proof.
  intros HGG [_ Hmx] Hvl Hvr; split; trivial => z v. in_dom_Gmon_graph.
  intros [Hv|Hv]; subst.
  - erewrite get_left_conv, get_right_conv, get_left_singleton,
          get_right_singleton; eauto.
    destruct vl as [xl|]; destruct vr as [xr|]; intros [Hl|Hr];
      try inversion Hl; try inversion Hr; subst; eauto.
  - erewrite get_left_conv', get_right_conv', <- Gmon_graph_dom; eauto.
Qed.

Local Hint Resolve maximal_op_singleton maximal_op get_left_singleton
  get_right_singleton.

Lemma maximally_marked_tree_both (G G' : Gmon) x xl xr :
  ✓ ((x [↦] (Some xl, Some xr)) ⋅ (G ⋅ G')) →
  xl ∈ dom (gset _) G → tree (Gmon_graph G) xl → maximal (Gmon_graph G) →
  xr ∈ dom (gset _) G' → tree (Gmon_graph G') xr → maximal (Gmon_graph G') →
  tree (Gmon_graph ((x [↦] (Some xl, Some xr)) ⋅ (G ⋅ G'))) x ∧
  maximal (Gmon_graph ((x [↦] (Some xl, Some xr)) ⋅ (G ⋅ G'))).
Proof.
  intros Hvl Hxl tl ml Hxr tr mr; split.
  - intros l. in_dom_Gmon_graph. intros [?|[HlG|HlG']]; first subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso. apply get_left_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_left_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto.
        - exfalso. apply get_right_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_right_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto. }
   + edestruct tl as [q [qv Hq]]; eauto.
     exists (true :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eapply path_conv_back in qv; eauto.
        - apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl. inversion Hl; subst.
          apply path_conv', path_conv in Hpv; eauto. erewrite Hq; eauto.
        - exfalso. apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl; inversion Hl; subst.
          do 2 apply path_conv' in Hpv; eauto. }
  + edestruct tr as [q [qv Hq]]; eauto.
     exists (false :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back'; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eapply path_conv_back' in qv; eauto.
        - exfalso. apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl; inversion Hl; subst.
          apply path_conv', path_conv in Hpv; eauto.
        - apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl. inversion Hl; subst.
          apply path_conv', path_conv' in Hpv; eauto. erewrite Hq; eauto. }
  - apply maximal_op_singleton; eauto.
Qed.

Lemma maximally_marked_tree_left (G : Gmon) x xl :
  ✓ ((x [↦] (Some xl, None)) ⋅ G) →
  xl ∈ dom (gset _) G → tree (Gmon_graph G) xl → maximal (Gmon_graph G) →
  tree (Gmon_graph ((x [↦] (Some xl, None)) ⋅ G)) x ∧
  maximal (Gmon_graph ((x [↦] (Some xl, None)) ⋅ G)).
Proof.
  intros Hvl Hxl tl ml; split.
  - intros l. in_dom_Gmon_graph. intros [?|HlG]; first subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso. apply get_left_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_left_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto.
        - exfalso. apply get_right_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_right_singleton in Hl; inversion Hl. }
   + edestruct tl as [q [qv Hq]]; eauto.
     exists (true :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eauto.
        - apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl. inversion Hl; subst.
          apply path_conv' in Hpv; eauto. erewrite Hq; eauto.
        - exfalso. apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl; inversion Hl. }
 - apply maximal_op_singleton; eauto.
Qed.

Lemma maximally_marked_tree_right (G : Gmon) x xr :
  ✓ ((x [↦] (None, Some xr)) ⋅ G) →
  xr ∈ dom (gset _) G → tree (Gmon_graph G) xr → maximal (Gmon_graph G) →
  tree (Gmon_graph ((x [↦] (None, Some xr)) ⋅ G)) x ∧
  maximal (Gmon_graph ((x [↦] (None, Some xr)) ⋅ G)).
Proof.
  intros Hvl Hxl tl ml; split.
  - intros l. in_dom_Gmon_graph. intros [?|HlG]; first subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso. apply get_left_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_left_singleton in Hl; inversion Hl.
        - exfalso. apply get_right_conv in Hl; [| |in_dom_Gmon_graph]; eauto.
          rewrite get_right_singleton in Hl; inversion Hl; subst.
          apply path_conv' in Hpv; eauto. }
   + edestruct tl as [q [qv Hq]]; eauto.
     exists (false :: q). split; [econstructor; eauto|].
     { eapply path_conv_back'; eauto; eapply path_conv_back; eauto. }
     { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - exfalso; eauto.
        - exfalso. apply get_left_conv in Hl; eauto.
          rewrite get_left_singleton in Hl; inversion Hl.
        - apply get_right_conv in Hl; eauto.
          rewrite get_right_singleton in Hl. inversion Hl; subst.
          apply path_conv' in Hpv; eauto. erewrite Hq; eauto. }
 - apply maximal_op_singleton; eauto.
Qed.

Lemma maximally_marked_tree_none (x : loc) :
  ✓ ((x [↦] (None, None)) : Gmon) →
  tree (Gmon_graph (x [↦] (None, None))) x ∧
  maximal (Gmon_graph (x [↦] (None, None))).
Proof.
  intros Hvl; split.
  - intros l. in_dom_Gmon_graph. intros ?; subst.
    + exists []; split.
      { constructor 1; trivial. in_dom_Gmon_graph; auto. }
      { intros p Hp. destruct p; inversion Hp as [| ? ? Hl Hpv| ? ? Hl Hpv];
          trivial; subst.
        - rewrite get_left_singleton in Hl; inversion Hl.
        - rewrite get_right_singleton in Hl; inversion Hl. }
 - split; trivial. intros z v. in_dom_Gmon_graph. intros ? [Hl|Hl]; subst.
    + rewrite get_left_singleton in Hl; inversion Hl.
    + rewrite get_right_singleton in Hl; inversion Hl.
Qed.

Lemma update_valid (G : Gmon) x v w : ✓ ((x [↦] v) ⋅ G) → ✓ ((x [↦] w) ⋅ G).
Proof.
  intros Hvl i; specialize (Hvl i); revert Hvl.
  rewrite ?lookup_op. destruct (decide (i = x)).
  - subst; rewrite ?lookup_singleton; case _ : (G !! x); done.
  - rewrite ?lookup_singleton_ne //=.
Qed.

Lemma of_graph_unmarked (g : graph loc) (G : Gmon) x v :
  of_graph g G !! x = Some (false, v) → g !! x = Some v.
Proof.
  rewrite lookup_imap /of_graph_elem lookup_omap.
  case _ : (g !! x); case _ : (G !! x) => [[]|]; by inversion 1.
Qed.
Lemma get_lr_disj (G G' : Gmon) i : ✓ (G ⋅ G') →
  (get_left (Gmon_graph (G ⋅ G')) i = get_left (Gmon_graph G) i ∧
   get_right (Gmon_graph (G ⋅ G')) i = get_right (Gmon_graph G) i ∧
   get_left (Gmon_graph G') i = None ∧
   get_right (Gmon_graph G') i = None) ∨
  (get_left (Gmon_graph (G ⋅ G')) i = get_left (Gmon_graph G') i ∧
   get_right (Gmon_graph (G ⋅ G')) i = get_right (Gmon_graph G') i ∧
   get_left (Gmon_graph G) i = None ∧
   get_right (Gmon_graph G) i = None).
Proof.
  intros Hvl. specialize (Hvl i). revert Hvl.
  rewrite /get_left /get_right /Gmon_graph ?lookup_omap ?lookup_op.
  case _ : (G !! i) => [[]|]; case _ : (G' !! i) => [[]|]; inversion 1;
    simpl; auto.
Qed.
Lemma mark_update_strict_subgraph (g : graph loc) (G G' : Gmon) : ✓ (G ⋅ G') →
  strict_subgraph g (Gmon_graph G) ∧ strict_subgraph g (Gmon_graph G') ↔
  strict_subgraph g (Gmon_graph (G ⋅ G')).
Proof.
  intros Hvl; split.
  - intros [HG HG'] i.
  destruct (get_lr_disj G G' i) as [(-> & -> & _ & _)|(-> & -> & _ & _)]; eauto.
  - intros HGG; split => i.
    + destruct (get_lr_disj G G' i) as [(<- & <- & _ & _)|(_ & _ & -> & ->)];
       eauto using strict_sub_children_None.
    + destruct (get_lr_disj G G' i) as [(_ & _ & -> & ->)|(<- & <- & _ & _)];
       eauto using strict_sub_children_None.
Qed.
Lemma strinct_subgraph_singleton (g : graph loc) x v :
  x ∈ dom (gset _) g → (∀ w, g !! x = Some w → strict_sub_children w v)
  ↔ strict_subgraph g (Gmon_graph (x [↦] v)).
Proof.
  rewrite elem_of_dom; intros [u Hu]; split.
  - move => /(_ _ Hu) Hgw i.
    rewrite /get_left /get_right /Gmon_graph lookup_omap.
    destruct (decide (i = x)); subst.
    + by rewrite Hu lookup_singleton; simpl.
    + rewrite lookup_singleton_ne; auto. by case _ : (g !! i) => [[[?|] [?|]]|].
  - intros Hg w Hw; specialize (Hg x). destruct v as [v1 v2]; simpl. revert Hg.
    rewrite Hu in Hw; inversion Hw; subst.
    by rewrite get_left_singleton get_right_singleton /get_left /get_right Hu.
Qed.
Lemma mark_strict_subgraph (g : graph loc) (G : Gmon) x v :
  ✓ ((x [↦] v) ⋅ G) → x ∈ dom (gset positive) g →
  of_graph g G !! x = Some (false, v) → strict_subgraph g (Gmon_graph G) →
  strict_subgraph g (Gmon_graph ((x [↦] v) ⋅ G)).
Proof.
  intros Hvl Hdx Hx Hsg. apply mark_update_strict_subgraph; try split; eauto.
  eapply strinct_subgraph_singleton; erewrite ?of_graph_unmarked; eauto.
  inversion 1; auto using strict_sub_children_refl.
Qed.
Lemma update_strict_subgraph (g : graph loc) (G : Gmon) x v w :
  ✓ ((x [↦] v) ⋅ G) → x ∈ dom (gset positive) g →
  strict_subgraph g (Gmon_graph ((x [↦] w) ⋅ G)) →
  strict_sub_children w v →
  strict_subgraph g (Gmon_graph ((x [↦] v) ⋅ G)).
Proof.
  intros Hvl Hdx Hx Hsc1 Hsc2.
  apply mark_update_strict_subgraph in Hx; eauto using update_valid.
  destruct Hx as [Hx1 Hx2].
  apply mark_update_strict_subgraph; try split; try tauto.
  pose proof (proj1 (elem_of_dom _ _) Hdx) as [u Hu].
  eapply strinct_subgraph_singleton in Hx1; eauto.
  apply strinct_subgraph_singleton; trivial.
  intros u' Hu'; rewrite Hu in Hu'; inversion Hu'; subst.
  intuition eauto using strict_sub_children_trans.
Qed.
