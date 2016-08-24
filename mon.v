From iris.heap_lang Require Export lifting heap notation.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre ghost_ownership tactics.
Import uPred.

From iris.algebra Require Import base cmra gmap.
From iris.prelude Require Import gmap mapset.

Require Import iris_spanning_tree.graph.

Local Arguments cmra_op _ !_ !_ / : simpl nomatch.
Local Arguments ucmra_op _ !_ !_ / : simpl nomatch.
Local Arguments op _ _ !_ !_ /.

(* This should be put in iris *)
Lemma None_op {A} (x : optionR A) : None ⋅ x = x.
Proof. by destruct x. Qed.

(* The monoid for talking about which nodes are marked.
These markings are duplicatable. *)
Definition markingUR : ucmraT := gmapUR loc unitR.

(** The CMRA we need. *)
Class markingG Σ := MarkingG {
  marking_inG :> authG heap_lang Σ markingUR;
  marking_name : gname
}.
(** The Functor we need. *)
Definition markingGF : gFunctor := authGF markingUR.

Section marking_definitions.
  Context `{Im : markingG Σ}.

  Definition is_marked_def (l : loc) : iPropG heap_lang Σ :=
    auth_own marking_name ({[ l := () ]} : markingUR).
  Definition is_marked_aux : { x | x = @is_marked_def }. by eexists. Qed.
  Definition is_marked := proj1_sig is_marked_aux.
  Definition is_marked_eq : @is_marked = @is_marked_def :=
    proj2_sig is_marked_aux.

  Lemma dup_marking (m : markingUR) : m ≡ m ⋅ m.
  Proof.
    intros i. rewrite lookup_op.
    match goal with
      |- ?B ≡ ?A ⋅ ?A => change B with A; by destruct A as [[]|]
    end.
  Qed.

  Notation "'μ(' x )" := (is_marked x) (format "μ( x )").

  Lemma dup_marked l : μ(l) ⊣⊢ μ(l) ★ μ(l).
  Proof. by rewrite is_marked_eq /is_marked_def -auth_own_op -dup_marking. Qed.

  Lemma new_marked_local_update (m : markingUR) l : ∅ ~l~> {[l := ()]} @ Some m.
  Proof.
    constructor.
    - intros n H1 i; specialize (H1 i); revert H1. simpl.
      rewrite ?lookup_op ?lookup_empty.
      match goal with
        |- ✓{n} (None ⋅ ?A) → ✓{n} ({[l := ()]} !! i ⋅ ?A) =>
        destruct A as [[]|]
      end;
        (destruct (decide (l = i)); subst;
         [rewrite lookup_singleton| rewrite lookup_singleton_ne]; eauto).
    - intros n [mz|]; simpl in *; rewrite ?ucmra_unit_left_id => H1 H2.
      + by rewrite H2.
      + by rewrite H2 ucmra_unit_right_id.
  Qed.

  Lemma new_marked_update {m} l :
    (● m ⋅ ◯ ∅) ~~> (● (m ⋅ {[l := () ]}) ⋅ ◯ ({[l := () ]} : markingUR)).
  Proof.
    rewrite <- (ucmra_unit_left_id m) at 1.
    rewrite (cmra_comm m).
    apply auth_update, new_marked_local_update.
  Qed.

  Lemma new_marked {E} (m : markingUR) l : own marking_name (● m) ⊢ |={E}=>
  own marking_name (● (m ⋅ {[l := () ]})) ★ μ(l).
  Proof.
    iIntros "H1".
    iPvs (auth_empty marking_name _) as "H2".
    unfold auth_own. iCombine "H1" "H2" as "H".
    iPvs (@own_update with "[H]") as "Y"; eauto.
    - eapply new_marked_update.
    - by rewrite is_marked_eq /is_marked_def /auth_own own_op.
  Qed.

  Lemma already_marked_op (m : markingUR) l :
    l ∈ dom (gset _) m → m ≡ m ⋅ {[l := () ]}.
  Proof.
    intros H i; rewrite lookup_op.
    destruct (proj1 (elem_of_dom _ _) H) as [[] H'].
    destruct (decide (i = l)); subst;
      by [rewrite H' lookup_singleton |
       rewrite lookup_singleton_ne //= comm None_op].
  Qed.

  Lemma already_marked {E} (m : markingUR) l :
    l ∈ dom (gset _) m → own marking_name (● m) ⊢ |={E}=>
  own marking_name (● m) ★ μ(l).
  Proof.
    iIntros (Hl) "Hm". iPvs (new_marked with "Hm") as "[H1 H2]"; iFrame.
    by rewrite -already_marked_op.
  Qed.

End marking_definitions.

Section marking_alloc.
  Context {Σ} (F : authG heap_lang Σ markingUR).

  Lemma marking_alloc {E} :
    True ⊢ |={E}=> ∃ G, @own _ _ _ (@auth_inG _ _ _ (@marking_inG Σ G))
                         (@marking_name Σ G) (● (∅ : markingUR)).
  Proof.
    iIntros "". iPvs (own_alloc (● (∅ : markingUR))) as (γ) "H".
    - split; auto using ucmra_unit_valid.
    - iPvsIntro. iExists (MarkingG _ _ _); eauto.
  Qed.

End marking_alloc.

Notation "'μ(' x )" := (is_marked x) (format "μ( x )").

(* Invariant token. This allows us to dispose the invariant. *)
Definition invtokUR : ucmraT := optionUR fracR.

(** The CMRA we need. *)
Class invtokG Σ := InvTokG {
  invtok_inG :> inG heap_lang Σ invtokUR;
  invtok_name : gname
}.
(** The Functor we need. *)
Definition invtokGF : gFunctor := authGF invtokUR.

Section invtok_definitions.
  Context `{Ii : invtokG Σ}.

  Definition token_def (q : Qp) : iPropG heap_lang Σ :=
    own invtok_name (Some q).
  Definition token_aux : { x | x = @token_def }. by eexists. Qed.
  Definition token := proj1_sig token_aux.
  Definition token_eq : @token = @token_def := proj2_sig token_aux.

  Notation "'κ(' q )" := (token q) (format "κ( q )").

  Lemma token_exclusive q : κ(1) ★ κ(q) ⊢ False.
  Proof.
    iIntros "H".
    rewrite token_eq /token_def -own_op.
    rewrite /auth_own own_valid. iDestruct "H" as %H. simpl in H.
    exfalso; eapply exclusive_l; [|exact H].
    typeclasses eauto.
  Qed.

  Definition packed_def P : iPropG heap_lang Σ := (κ(1) ∨ P)%I.
  Definition packed_aux : { x | x = @packed_def }. by eexists. Qed.
  Definition packed := proj1_sig packed_aux.
  Definition packed_eq : @packed = @packed_def := proj2_sig packed_aux.

  Notation "'ρκ(' P )" := (packed P) (format "ρκ( P )").

  Lemma UnPack q P : κ(q) ★ ρκ(P) ⊢ P ★ κ(q).
  Proof.
    rewrite packed_eq /packed_def.
    iIntros "[H1 [H2|H2]]".
    - iExFalso; iApply token_exclusive; iSplitL "H2"; eauto.
    - iSplitL "H2"; trivial.
  Qed.

  Lemma UnPack_later q P : ▷ κ(q) ★ ▷ ρκ(P) ⊢ ▷ P ★ ▷ κ(q).
  Proof. by iIntros; iNext; iApply UnPack. Qed.

  Lemma Pack P : P ⊢ ρκ(P).
  Proof.
    rewrite packed_eq /packed_def.
    by iIntros "H"; iRight.
  Qed.

  (* This gives you back the packages but disposes the key to unpack it. *)
  Lemma Dispose P : κ(1) ★ ρκ(P) ⊢ P ★ ρκ(P).
  Proof.
    rewrite packed_eq /packed_def.
    iIntros "[H1 [H2|H2]]".
    - iExFalso; iApply token_exclusive; iSplitL "H2"; eauto.
    - iSplitL "H2"; auto.
  Qed.

End invtok_definitions.

(* This should provided as part of iris. *)
Lemma OneValid : ✓ 1%Qp.
Proof. cbv; congruence. Qed.

Notation "'κ(' q )" := (token q) (format "κ( q )").
Notation "'ρκ(' P )" := (packed P) (format "ρκ( P )").

Section invtok_alloc.
  Context {Σ} (F : inG heap_lang Σ invtokUR).

  Lemma invtok_alloc {E} P :
    P ⊢ |={E}=> ∃ G, (@token Σ G 1) ★ (@packed Σ G P).
  Proof.
    iIntros "H1". iPvs (@own_alloc _ _ _ F (Some 1%Qp)) as (γ) "H2".
    - apply OneValid.
    - iPvsIntro. iExists (InvTokG _ _ _).
      rewrite token_eq. iSplitR "H1"; eauto. by iApply @Pack.
  Qed.

End invtok_alloc.

(* children cofe *)
Canonical Structure chlC := leibnizC (option loc * option loc)%type.
(* The graph monoid. *)
Definition graphN : namespace := nroot .@ "SPT_graph".
Definition graphUR : ucmraT :=
  optionUR (prodR fracR (gmapR loc (optionR (exclR chlC)))).

(** The CMRA we need. *)
Class graphG Σ := GraphG {
  graph_inG :> authG heap_lang Σ graphUR;
  graph_name : gname
}.
(** The Functor we need. *)
Definition graphGF : gFunctor := authGF graphUR.

Definition pr_opl_heap (w : (option loc * option loc)) : val:=
  match w with
  | (Some l, Some l') => (SOMEV #l, SOMEV #l')
  | (Some l, None) => (SOMEV #l, NONEV)
  | (None, Some l') => (NONEV, SOMEV #l')
  | (None, None) => (NONEV, NONEV)
  end.

(* convert the data of a node to a value in the heap *)
Definition ND_to_heap (v : bool * (option loc * option loc)) : val * val :=
  match v with
  | (m, w) => (#m, pr_opl_heap w)
  end.

Definition to_graph_elem (v : bool * (option loc * option loc)) :
  (optionR (exclR chlC)) :=
  match v with
  | (m, w) =>
    if m then Some (Excl w) else None
  end.

Definition to_base_graph (g : graph loc) :
  (gmapR loc (optionR (exclR chlC)))
  := fmap to_graph_elem g.

Definition to_graph (g : graph loc) : graphUR := Some (1%Qp, to_base_graph g).

Definition of_graph_elem (g : graph loc) i v
  : option (bool * (option loc * option loc)) :=
  match v with
  | None => g !! i
  | Some u => match u with
             | Excl w => Some (true, w)
             | _ => None
             end
  end.

Definition of_base_graph (g : graph loc)
           (γ : (gmapR loc (optionR (exclR chlC))))
  : graph loc := (map_imap (of_graph_elem g) γ).

Definition of_graph (g : graph loc) (γ : graphUR) : graph loc :=
  match γ with
  | Some (_, δ) => of_base_graph g δ
  | None => ∅
  end.

Section definitions.
  Context `{Ih : heapG Σ} `{Ii : invtokG Σ} `{Im : markingG Σ} `{Ig : graphG Σ}.

  Definition own_graph_def q γ : iPropG heap_lang Σ :=
    own graph_name (◯ (Some (q, γ) : graphUR)).
  Definition own_graph_aux : { x | x = @own_graph_def }. by eexists. Qed.
  Definition own_graph := proj1_sig own_graph_aux.
  Definition own_graph_eq : @own_graph = @own_graph_def :=
    proj2_sig own_graph_aux.

  Global Instance own_graph_proper q : Proper ((≡) ==> (⊣⊢)) (own_graph q).
  Proof. rewrite own_graph_eq /own_graph_def. intros ? ? H. by rewrite H. Qed.

  Definition graph_inv (g : graph loc) (Mrk : gmap loc loc)
    : iPropG heap_lang Σ :=
    (∃ γ μ,
        (own graph_name (● (Some (1%Qp, γ) : graphUR)))
          ★ (own marking_name (● (μ : markingUR)))
          ★ ([★ map] l ↦ v ∈ (of_base_graph g γ),
             ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                          ★ m ↦ (ND_to_heap v).1)
          ★ (dom (gset _) μ = marked (of_base_graph g γ))
          ★ (dom (gset _) γ = dom (gset _) g)
    )%I.

  Definition graph_ctx g Mrk : iPropG heap_lang Σ :=
    inv graphN ρκ(graph_inv g Mrk).

  Global Instance graph_ctx_persistent g Mrk : PersistentP (graph_ctx g Mrk).
  Proof. apply _. Qed.
End definitions.

Notation "'Γρ(' q , γ )" := (own_graph q γ) (format "'Γρ(' q ,  γ )").

Notation "'Γρ(' q , l [↦] v )" :=
  (own_graph q {[l := v]}) (format "'Γρ(' q ,  l  [↦]  v )").

Typeclasses Opaque graph_ctx own_graph.
Instance: Params (@graph_inv) 1.
Instance: Params (@own_graph) 5.
Instance: Params (@graph_ctx) 4.

Section graph.
  Context {Σ : gFunctors}.
  Implicit Types P Q : iPropG heap_lang Σ.
  Implicit Types Φ : val → iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h : heapUR.

  Lemma to_base_graph_dom g :
    dom (gset _) (to_base_graph g) = dom (gset _) g.
  Proof.
    apply mapset_eq=>i. rewrite ?elem_of_dom /is_Some /to_base_graph lookup_fmap.
    unfold graph, loc in *.
    destruct (g !! i) as [[[] ?]|]; simpl; split; eauto.
    all : intros [? H]; inversion H.
  Qed.
  Lemma of_base_graph_dom g γ :
    ✓ γ →
    dom (gset _) g = dom (gset _) γ →
    dom (gset _) (of_base_graph g γ) = dom (gset _) g.
  Proof.
    intros H1 H2.
    set (H2' := proj1 (mapset_eq _ _) H2); clearbody H2'; clear H2.
    apply mapset_eq=>i. specialize (H2' i); specialize (H1 i). revert H2'.
    rewrite ?elem_of_dom /is_Some /of_base_graph /of_graph_elem lookup_imap.
    unfold graph, loc in *.
    match goal with
      |- _ ↔ (∃ x, ?A = _) → (∃ x, ?B ≫= _ = _) ↔ (∃ x, _ = _) =>
      change B with A; destruct A as [[[]|]|]; destruct (g !! i);
        simpl; intros [H21 H22]; split => H3; eauto; try inversion H1
    end.
    match type of H21 with
      ?A → ?B => assert (H4 : B → False); [|exfalso; apply H4]; eauto
    end. intros [? H4]; inversion H4.
  Qed.

  Lemma of_base_graph_op_combine g γ γ' :
    marked g = ∅ → ✓ (γ ⋅ γ') → dom (gset _) g = dom (gset _) γ →
    dom (gset _) g = dom (gset _) γ' →
    of_base_graph g (γ ⋅ γ') =
    combine_graphs (of_base_graph g γ) (of_base_graph g γ').
  Proof.
    intros Hgm H1 H2 H3. eapply @map_eq; [typeclasses eauto|] => i.
    set (Hgm' := proj1 (mapset_eq _ _) Hgm); clearbody Hgm'; clear Hgm.
    set (H2' := proj1 (mapset_eq _ _) H2); clearbody H2'; clear H2.
    set (H3' := proj1 (mapset_eq _ _) H3); clearbody H3'; clear H3.
    specialize (H2' i); specialize (H3' i); specialize (H1 i);
      specialize (Hgm' i). revert Hgm' H1 H2' H3'. rewrite /combine_graphs.
    erewrite lookup_merge; [| apply combine_node_data_DiagNone].
    rewrite ?elem_of_dom /is_Some /of_base_graph /of_graph_elem
            ?lookup_imap lookup_op /marked  elem_of_mapset_dom_with
            elem_of_empty. unfold graph, loc in *.
    match goal with
      |- _ → ✓ (?A0 ⋅ ?B0) → _ ↔ (∃ x, ?A0 = _) → _ ↔ (∃ x, ?B0 = _) →
        (?A0 ⋅ ?B0) ≫= _ = combine_node_data (?A1 ≫= _) (?B1 ≫= _) =>
      change A1 with A0; change B1 with B0;
        destruct A0 as [[[[]|]|]|]; destruct B0 as [[[[]|]|]|]; trivial;
          destruct (g !! i) as [[[] []]|]; simpl;
            intros [Hgm' _] H1 [H21 H22] [H31 H32]; trivial;
              try (exfalso; apply Hgm'; eauto; fail);
              try
                match goal with
                  H : _ → ∃ x, None = Some x |- _ =>
                  match type of H with
                    _ → ?B =>
                    assert (B → False);
                      [let H' := fresh in intros [? H'];inversion H'
                      | exfalso; eauto]
                  end
            end
    end.
    unfold bool_decide; repeat destruct option_eq_dec; simpl; tauto.
  Qed.

  (** Conversion to heaps and back *)
  Global Instance of_graph_proper g : Proper ((≡) ==> (=)) (of_graph g).
  Proof. solve_proper. Qed.

  Lemma from_to_base_graph g : of_base_graph g (to_base_graph g) = g.
  Proof.
    unfold graph in *.
    apply map_eq =>l. rewrite lookup_imap lookup_fmap.
    unfold of_graph_elem, graph. case (g !! l); trivial.
    by intros [[] w].
  Qed.
  Lemma to_graph_valid g : ✓ to_graph g.
  Proof.
    split. apply OneValid.
    intros l. rewrite lookup_fmap. unfold graph in *. case (g !! l); simpl.
    - intros [[] w]; constructor.
    - constructor.
  Qed.

  Section graph_ctx_alloc.
    Context `{Ih : heapG Σ} (F1 : authG heap_lang Σ markingUR)
            (F2 : inG heap_lang Σ invtokUR) (F3 : authG heap_lang Σ graphUR).

    Lemma graph_ctx_alloc (E : coPset) (g : graph loc) (Mrk : gmap loc loc)
          (Hme : marked g = ∅)
          (HNE : (nclose graphN) ⊆ E)
      :
        ([★ map] l ↦ v ∈ g,
         ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                      ★ m ↦ (ND_to_heap v).1)
          ⊢ |={E}=> ∃ Im Ig Ii, κ(1) ★ @graph_ctx _ _ Ii Im Ig g Mrk ★
                                Γρ(1%Qp, (to_base_graph g)).
    Proof.
      iIntros "H1".
      iPvs (marking_alloc) as (Im) "H2"; iExists Im.
      iPvs (own_alloc (● (to_graph g) ⋅ ◯ (to_graph g))) as (γ) "H3".
      { split; auto using to_graph_valid. }
      iDestruct "H3" as "[H31 H32]".
      set (Ig := GraphG _ _ γ). iExists _.
      iAssert (graph_inv g Mrk) with "[H1 H2 H31]" as "H".
      { unfold graph_inv. iExists (to_base_graph g), ∅.
        iFrame "H2 H31".
        iSplitL. by rewrite from_to_base_graph.
        iSplit; iPureIntro.
        - by rewrite from_to_base_graph dom_empty_L.
        - apply to_base_graph_dom. }
      iPvs (invtok_alloc F2 (graph_inv g Mrk) with "[H]") as (Ii) "[H1 H2]";
        trivial.
      iExists _. iFrame "H1".
      iPvs (inv_alloc graphN E with "[H2]") as "H"; eauto.
      iPvsIntro. rewrite /graph_ctx /to_graph own_graph_eq.
      by iFrame "H H32".
    Qed.

  End graph_ctx_alloc.


  Lemma graph_expose_node g γ i v :
    marked g = ∅ →
    of_base_graph g γ !! i = Some v →
    γ = {[i := to_graph_elem v]} ⋅ (delete i γ).
  Proof.
    intros H1 H2; eapply @map_eq; try typeclasses eauto; intros x;
      rewrite lookup_op.
    set (H1' := proj1 (proj1 (mapset_eq _ _) H1 i)); clearbody H1'; clear H1.
    revert H1';rewrite /marked elem_of_mapset_dom_with elem_of_empty; intros H1.
    destruct (decide (x = i)); subst;
      [rewrite lookup_singleton lookup_delete|
       rewrite lookup_singleton_ne; [rewrite lookup_delete_ne|]]; auto.
    - revert H2. simpl. rewrite /of_base_graph lookup_imap.
      match goal with
        |- ?A ≫= _ = _ → ?B = _ =>
        change B with A; destruct A as [[[]|]|];
          try (intros H2; inversion H2; trivial; fail); simpl
      end. revert H1.
      match goal with
        |- ((∃ x, ?A = _ ∧ _) → _) → ?B = _ → _ =>
        change B with A; destruct A; intros H1 H2; inversion H2; subst
      end.
      destruct v as [[] ?]; simpl; trivial. exfalso; eauto.
    - by match goal with |- ?A = _ => destruct A end.
  Qed.

  Lemma graph_equiv_eq (γ γ' : gmapR loc (optionR (exclR chlC))) :
    γ ≡ γ' → γ = γ'.
  Proof.
    intros H1. eapply @map_eq; try typeclasses eauto. intros i.
    specialize (H1 i). revert H1.
    match goal with
      |- ?A1 ≡ ?B1 → ?A = ?B =>
      change A1 with A; change B1 with B;
        destruct A as [[[]|]|]; destruct B as [[[]|]|];
          intros H1; inversion H1 as [? ? H2|]; subst;
            try inversion H2 as [? ? H3|]; subst;
              try inversion H3 as [? ? H4|]; subst;
                try inversion H4; subst; trivial
    end.
  Qed.

  Context {Ih : heapG Σ} {Im : markingG Σ} {Ig : graphG Σ} {Ii : invtokG Σ}.

  Lemma whole_frac γ γ':
    (own graph_name (● (Some (1%Qp, γ) : graphUR)) ★ Γρ(1%Qp, γ'))
      ⊢
      own graph_name (● (Some (1%Qp, γ) : graphUR)) ★ Γρ(1%Qp, γ') ★ γ = γ'.
  Proof.
    iIntros "[H1 H2]". rewrite own_graph_eq /own_graph_def.
    rewrite assoc -own_op. iCombine "H1" "H2" as "H".
    iDestruct (@own_valid with "#H") as %[H1 H2]; cbn in *.
    iFrame "H"; iPureIntro. apply graph_equiv_eq, equiv_dist => n.
    specialize (H1 n). destruct H1 as [[[q u]|] H1].
    - revert H1; rewrite -Some_op pair_op => H1.
      edestruct (λ H, dist_Some_inv_l _ _ _ H H1) as [z [H31 [H41 H42]]];
        try inversion H31; subst; eauto. simpl in *.
      assert (H51 : ✓ (1%Qp ⋅ q)) by (rewrite -H41; apply OneValid).
      exfalso; eapply exclusive_l; eauto; try typeclasses eauto.
    - inversion H1 as [? ? H3|]; subst; inversion H3; trivial.
  Qed.

  Lemma auth_own_graph_valid q γ :
    own graph_name (● (Some (q, γ) : graphUR))
        ⊢ own graph_name (● (Some (q, γ) : graphUR)) ★ ✓ γ.
  Proof.
    iIntros "H1".
    iDestruct (@own_valid with "#H1") as %[H1 [H21 H22]]; eauto.
  Qed.

  Lemma own_graph_valid q γ : Γρ(q, γ) ⊢ Γρ(q, γ) ★ ✓ γ.
  Proof.
    iIntros "H1". rewrite own_graph_eq /own_graph_def.
    iDestruct (@own_valid with "#H1") as %[H1 H2]; eauto.
  Qed.

  Lemma graph_split q1 q2 g1 g2 :
    Γρ((q1 + q2)%Qp, g1 ⋅ g2) ⊣⊢ Γρ(q1, g1) ★ Γρ(q2, g2).
  Proof. by rewrite own_graph_eq /own_graph_def -own_op. Qed.

  Lemma unmarked_all_Nones g γ :
    ✓ γ → marked (of_base_graph g γ) = ∅ →
    ∀ i, i ∈ dom (gset _) γ → γ !! i = Some None.
  Proof.
    intros H1 H2 i H3; specialize (H1 i).
    set (H2' := proj1 (mapset_eq _ _) H2 i); clearbody H2'; clear H2.
    destruct H2' as [H2 _]. revert H1 H2 H3.
    rewrite elem_of_mapset_dom_with elem_of_empty lookup_imap ?elem_of_dom
            /is_Some /of_graph_elem; cbn.
    match goal with
      |- ✓ ?C → ((∃ x, ?A ≫= _ = _ ∧ _) → False) → (∃ x, ?D = _) → ?B = _ =>
      change B with A; change C with A; change D with A;
        destruct A as [[[]|]|]; eauto
    end; simpl; try (inversion 1; fail).
    - intros ? H1; exfalso; apply H1; eauto.
    - intros ? ? [? H1]; inversion H1.
  Qed.

  Lemma graph_op_right_unit g γ1 γ2 :
    ✓ (γ1 ⋅ γ2) →
    dom (gset _) γ1 = dom (gset _) γ2 →
    marked (of_base_graph g γ2) = ∅ → γ1 ⋅ γ2 ≡ γ1.
  Proof.
    unfold marked, of_base_graph. intros H1 H2 H3.
    set (H2' := proj1 (mapset_eq _ _) H2); clearbody H2'; clear H2.
    set (H3' := proj1 (mapset_eq _ _) H3); clearbody H3'; clear H3.
    intros i. specialize (H2' i); specialize (H3' i); specialize (H1 i).
    rewrite lookup_op; rewrite lookup_op in H1.
    destruct H3' as [H3' _]. revert H2' H3' H1.
    rewrite elem_of_mapset_dom_with elem_of_empty lookup_imap ?elem_of_dom
    /is_Some; cbn.
    match goal with
      |-
      (∃ x, ?A1 = _) ↔ (∃ x, ?B1 = _) →
      ((∃ x, ?B2 ≫= _ = _ ∧ _) → False) →
      ✓ (?A2 ⋅ ?B3) →
      ?A ⋅ ?B ≡ ?A3 =>
      change A1 with A; change A2 with A; change A3 with A; change B1 with B;
        change B2 with B; change B3 with B;
        destruct A as [[[[]| ]|]|];
        destruct B as [[[[]| ]|]|]; simpl; trivial
    end.
    all : intros H2' H3' H1.
    all : try (exfalso; apply H3'; eauto; fail).
    all : try (inversion H1).
    destruct H2' as [_ H2'].
    match type of H2' with
      ?A → ?B => assert (H4 : B → False); [| exfalso; apply H4; eauto]
    end.
    intros [? H5]; inversion H5.
  Qed.

  Lemma graph_op_left_unit g γ1 γ2 :
    ✓ (γ1 ⋅ γ2) →
    dom (gset _) γ1 = dom (gset _) γ2 →
    marked (of_base_graph g γ1) = ∅ → γ1 ⋅ γ2 ≡ γ2.
  Proof.
    rewrite (comm _ γ1). intros H1 H2 H3.
    eapply graph_op_right_unit; eauto.
  Qed.

  Lemma own_graph_get_singleton_graph g γ x :
    ✓ γ →
    x ∈ dom (gset _) γ →
    marked (of_base_graph g γ) = ∅ → γ = {[ x := None]} ⋅ γ.
  Proof.
    intros H1 H2 H3.
    eapply @map_eq; try typeclasses eauto. intros i.
    rewrite lookup_op.
    destruct (decide (i ∈ dom (gset _) γ)) as [|Hn].
    - erewrite unmarked_all_Nones; eauto.
      destruct (decide (x = i)); subst;
        [rewrite lookup_insert| rewrite lookup_insert_ne]; auto.
    - destruct (decide (x = i)); subst; try tauto.
      rewrite lookup_insert_ne; auto. rewrite lookup_empty.
      rewrite (proj1 (not_elem_of_dom _ _) Hn); eauto.
  Qed.

  Lemma graph_divide q (γ γ' : (gmapR loc (optionR (exclR chlC)))) :
    (((q / 2)%Qp, γ) ⋅ ((q / 2)%Qp, γ')) ≡ (q, γ ⋅ γ').
  Proof.
    rewrite pair_op.
    change ((q / 2)%Qp ⋅ (q / 2)%Qp) with ((q / 2) + (q / 2))%Qp.
      by rewrite Qp_div_2.
  Qed.

  Lemma own_graph_get_singleton g q γ x :
    x ∈ dom (gset _) γ →
    marked (of_base_graph g γ) = ∅ →
    Γρ(q, γ) ⊣⊢ Γρ((q / 2)%Qp, x [↦] None) ★ Γρ((q / 2)%Qp, γ).
  Proof.
    iIntros (H1 H2); iSplit.
    - iIntros "H1". iDestruct (own_graph_valid with "H1") as "[H1 %]".
      rewrite own_graph_eq /own_graph_def.
      rewrite -own_op -auth_frag_op -Some_op. rewrite graph_divide.
      erewrite <- own_graph_get_singleton_graph; eauto.
    - iIntros "[H1 H2]". iDestruct (own_graph_valid with "H2") as "[H2 %]".
      rewrite own_graph_eq /own_graph_def. iCombine "H1" "H2" as "H".
      rewrite -auth_frag_op -Some_op. rewrite graph_divide.
      erewrite <- own_graph_get_singleton_graph; eauto.
  Qed.

  Lemma graph_dist_equiv (γ γ' : (gmapR loc (optionR (exclR chlC)))) n
    : γ ≡{n}≡ γ' → γ ≡ γ'.
  Proof.
    intros H i. specialize (H i). revert H.
    match goal with
      |- ?A ≡{_}≡ ?B → ?A ≡ ?B => destruct A; destruct B; try (inversion 1; fail)
    end; trivial.
    inversion 1 as [? ? H1|]; subst; trivial.
    inversion H1 as [? ? H2|]; subst; trivial.
    inversion H2 as [? ? ? H3|]; subst; trivial.
    inversion H3; subst; trivial.
  Qed.

  Lemma auth_subgraph (q q' : Qp) (γ γ' : (gmapR loc (optionR (exclR chlC)))) :
    ✓ (● Some (q, γ) ⋅ ◯ Some (q', γ')) →
    ∀ i, i ∈ dom (gset _) γ' → i ∈ dom (gset _) γ.
  Proof.
    intros [H1 H2]; simpl in *.
    specialize (H1 O).
    revert H1. intros [[[s u]|] H1].
    - inversion H1 as [? ? H3|]; subst; clear H1.
      destruct H3 as [_ H3]. eapply graph_dist_equiv in H3; simpl in *.
      rewrite (graph_equiv_eq _ _ H3). intros i; specialize (H3 i); revert H3.
      rewrite ?elem_of_dom /is_Some ?lookup_op.
      destruct H2 as [_ H2]; specialize (H2 i); simpl in H2; revert H2.
      match goal with
        |- ✓ ?A1 → ?A2 ≡ ?B1 ⋅ ?C1 → (∃ x, ?B2 = _) → ∃ x, ?B3 ⋅ ?C2 = _ =>
        change A2 with A1; change B3 with B1; change B2 with B1;
          change C2 with C1;
          destruct A1 as [[[]|]|]; destruct B1 as [[[]|]|];
            destruct C1 as [[[]|]|]; simpl in *;
              intros H1 H2; inversion H1; inversion H2;
                eauto
      end.
    - inversion H1 as [? ? H3|]; subst; clear H1.
      destruct H3 as [_ H3]. simpl in *.
      by rewrite (graph_equiv_eq _ _ (graph_dist_equiv _ _ _ H3)).
  Qed.

  Lemma graph_in_mem_valid_point γ q x m :
    (own graph_name (● (Some (q, {[x := m]} ⋅ γ) : graphUR))) ⊢ ✓ m.
  Proof.
    iIntros "H1". iDestruct (@own_valid with "H1") as %H.
    destruct H as [_ [_ H]]; simpl in *. specialize (H x); revert H.
    rewrite lookup_op lookup_singleton; intros H. by apply cmra_valid_op_l in H.
  Qed.

  Lemma marking_updating_validN
        {n} (γ : (gmapR loc (optionR (exclR chlC)))) (q : frac) x w m :
    ✓ w →
    γ !! x = None → ✓{n} Some (q, {[x := m]} ⋅ γ) →
    ✓{n} Some (q, {[x := Some w]} ⋅ γ).
  Proof.
    intros Hw H1 [H21 H22]; split; trivial; simpl in *.
    intros i; specialize (H22 i); revert H22; rewrite ?lookup_op.
    destruct (decide (i = x)); subst;
      [rewrite ?lookup_singleton| rewrite ?lookup_singleton_ne]; auto.
    rewrite H1; trivial.
  Qed.

  Lemma valid_op_option_excl (m w : optionR (exclR chlC)) n :
    ✓ m → m ≡{n}≡ m ⋅ w → w = None.
  Proof.
    intros H1 H2.
    assert (H3: ✓{n} (m ⋅ w)) by (by rewrite -H2).
    destruct m as [[]|]; destruct w as [[]|];
      inversion H1; inversion H2; inversion H3; simpl; trivial.
  Qed.

  Lemma mark_update_graph {E} γ q x w m :
    ✓ w →
    γ !! x = None →
    ((own graph_name (● (Some (1%Qp, {[x := m]} ⋅ γ) : graphUR)))
       ★ Γρ(q, x [↦] m))
      ⊢ |={E}=> ((own graph_name
                     (● (Some (1%Qp, {[x := Some w]} ⋅ γ) : graphUR)))
           ★ Γρ(q, x [↦] Some w)).
  Proof.
    intros Hw H.
    iIntros "[H1 H2]". iDestruct (graph_in_mem_valid_point with "#H1") as %H'.
    iCombine "H1" "H2" as "H".
    rewrite ?own_graph_eq /own_graph_def -?own_op -?auth_both_op.
    iPvs (@own_update with "H") as "H'"; eauto.
    intros n [[[mza|] [[qo mzo]|]]|]; simpl;
      rewrite /validN /cmra_validN //= /auth_validN; simpl.
    - intros [[u H1] H2]; split.
      + destruct u as [[qu u]|].
        * inversion H1 as [? ? [H31 H32]|]; subst. eexists (Some (qu, u)).
          constructor; split; simpl in *; trivial.
          intros i; specialize (H32 i); revert H32.
          rewrite ?lookup_op; destruct (decide (i = x)); subst;
            [rewrite ?lookup_singleton H| rewrite ?lookup_singleton_ne //=].
          match goal with
            |- _ ≡{n}≡ _ ⋅ ?A ⋅ ?B → _ ≡{n}≡ _ ⋅ ?A ⋅ ?B =>
            destruct A; destruct B; simpl; inversion 1 as [? ? H4|]; subst;
              try (revert H4; rewrite -?assoc; intros H4);
            try rewrite (valid_op_option_excl _ _ _ _ H4); trivial
          end.
        * exists None; simpl in *.
          inversion H1 as [? ? [H31 H32]|]; subst.
          constructor; split; simpl in *; trivial.
          intros i; specialize (H32 i); revert H32.
          rewrite ?lookup_op; destruct (decide (i = x)); subst;
            [rewrite ?lookup_singleton H| rewrite ?lookup_singleton_ne //=].
          match goal with
            |- _ ≡{n}≡ _ ⋅ ?A → _ ≡{n}≡ _ ⋅ ?A =>
            destruct A; simpl; inversion 1 as [? ? H4|]; subst;
              try (revert H4; rewrite -?assoc; intros H4);
            try rewrite (valid_op_option_excl _ _ _ _ H4); trivial
          end.
      + by eapply marking_updating_validN.
    - intros [[u H1] H2]; split.
      + destruct u as [[qu u]|].
        * inversion H1 as [? ? [H31 H32]|]; subst. eexists (Some (qu, u)).
          constructor; split; simpl in *; trivial.
          intros i; specialize (H32 i); revert H32.
          rewrite ?lookup_op; destruct (decide (i = x)); subst;
            [rewrite ?lookup_singleton H| rewrite ?lookup_singleton_ne //=].
          match goal with
            |- _ ≡{n}≡ _ ⋅ ?A → _ ≡{n}≡ _ ⋅ ?A =>
            destruct A; simpl; inversion 1 as [? ? H4|]; subst;
              try (revert H4; rewrite -?assoc; intros H4);
            try rewrite (valid_op_option_excl _ _ _ _ H4); trivial
          end.
        * exists None; simpl in *.
          inversion H1 as [? ? [H31 H32]|]; subst.
          constructor; split; simpl in *; trivial.
          intros i; specialize (H32 i); revert H32.
          rewrite ?lookup_op; destruct (decide (i = x)); subst;
            by [rewrite ?lookup_singleton H| rewrite ?lookup_singleton_ne //=].
      + by eapply marking_updating_validN.
    - intros [[u H1] H2]; split.
      + destruct u as [[qu u]|].
        * inversion H1 as [? ? [H31 H32]|]; subst. eexists (Some (qu, u)).
          constructor; split; simpl in *; trivial.
          intros i; specialize (H32 i); revert H32.
          rewrite ?lookup_op; destruct (decide (i = x)); subst;
            [rewrite ?lookup_singleton H| rewrite ?lookup_singleton_ne //=].
          match goal with
            |- _ ≡{n}≡ _ ⋅ ?A → _ ≡{n}≡ _ ⋅ ?A =>
            destruct A; simpl; inversion 1 as [? ? H4|]; subst;
              try (revert H4; rewrite -?assoc; intros H4);
            try rewrite (valid_op_option_excl _ _ _ _ H4); trivial
          end.
        * exists None; simpl in *.
          inversion H1 as [? ? [H31 H32]|]; subst.
          constructor; split; simpl in *; trivial.
          intros i; specialize (H32 i); revert H32.
          rewrite ?lookup_op; destruct (decide (i = x)); subst;
            by [rewrite ?lookup_singleton H| rewrite ?lookup_singleton_ne //=].
      + by eapply marking_updating_validN.
  Qed.

  Lemma graph_pointsto_marked γ q x w v :
    γ !! x = None →
    ((own graph_name (● (Some (1%Qp, {[x := v]} ⋅ γ) : graphUR)))
       ★ Γρ(q, x [↦] Some w))
      ⊢ ((own graph_name (● (Some (1%Qp, {[x := v]} ⋅ γ) : graphUR)))
           ★ Γρ(q, x [↦] Some w) ★ v = Some w).
  Proof.
    intros H. rewrite own_graph_eq /own_graph_def assoc -?own_op.
    iIntros "H"; iDestruct (@own_valid with "#H") as %[H1 H1']; simpl in *.
    iFrame. iPureIntro. specialize (H1 O). destruct H1 as [z H1].
    inversion H1 as [u [q' y] [_ H2] H3 H4|]; subst; simpl in *.
    apply graph_dist_equiv, graph_equiv_eq in H2; subst.
    destruct z as [[q'' z]|].
    - inversion H4 as [[H21 H22]]; subst. rewrite H22 in H1'.
      inversion H1' as [_ H12]; specialize (H12 x); simpl in *; clear H1'.
      revert H12; rewrite lookup_op lookup_singleton; intros H12.
      match type of H22 with
        ?A = ?B => assert (H3: A !! x = B !! x) by (by rewrite H22)
      end. revert H3; rewrite ?lookup_op ?lookup_singleton H.
      match goal with
        |- _ = _ ⋅ ?B → _ =>
        destruct B as [[]|]; repeat (unfold op, cmra_op; simpl); by inversion 1
      end.
    - inversion H4 as [[H21 H22]]; subst.
      match type of H22 with
        ?A = ?B => assert (H3: A !! x = B !! x) by (by rewrite H22)
      end. revert H3; rewrite ?lookup_op ?lookup_singleton H. by inversion 1.
  Qed.

  Lemma graph_open g Mrk γ q x w
    :
      (dom (gset loc) γ = dom (gset loc) g)
        ★ (own graph_name (● (Some (1%Qp, γ) : graphUR)))
        ★ ([★ map] l ↦ v ∈ (of_base_graph g γ),
           ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                        ★ m ↦ (ND_to_heap v).1)
        ★ Γρ(q, x [↦] w)
        ⊢ (dom (gset loc) γ = dom (gset loc) g)
        ★ (own graph_name (● (Some (1%Qp, γ) : graphUR)))
        ★ ([★ map] l ↦ v ∈ delete x (of_base_graph g γ),
           ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                        ★ m ↦ (ND_to_heap v).1)
        ★ (∃ u, (of_base_graph g γ !! x = Some u)
                  ★ ∃ (m : loc), Mrk !! x = Some m ★ x ↦ (#m, (ND_to_heap u).2)
                                                 ★ m ↦ (ND_to_heap u).1)
        ★ Γρ(q, x [↦] w).
  Proof.
    iIntros "(Hd & Hg & Ha & Hl)". rewrite own_graph_eq /own_graph_def.
    iCombine "Hg" "Hl" as "Hg". iDestruct (@own_valid with "#Hg") as %Hvalid.
    iDestruct "Hg" as "[Hg Hl]". iDestruct "Hd" as %Hd.
    iDestruct (auth_own_graph_valid with "Hg") as "[Hg %]". iFrame "Hg Hl".
    iSplitR; trivial.
    assert (Hid : x ∈ dom (gset _) (of_base_graph g γ)).
    { rewrite of_base_graph_dom; auto. rewrite -Hd.
      eapply auth_subgraph; eauto; by rewrite dom_singleton elem_of_singleton.
    } revert Hid; rewrite elem_of_dom /is_Some. intros [y Hy].
    rewrite -{1}(insert_id _ _ _ Hy) -insert_delete.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
    iDestruct "Ha" as "[H $]". iExists _;  eauto.
  Qed.

  Lemma graph_open_later g Mrk γ q x w :
    ▷ (dom (gset loc) γ = dom (gset loc) g)
      ★ ▷ (own graph_name (● (Some (1%Qp, γ) : graphUR)))
      ★ ▷ ([★ map] l ↦ v ∈ (of_base_graph g γ),
           ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                        ★ m ↦ (ND_to_heap v).1)
      ★ ▷ Γρ(q, x [↦] w)
      ⊢ ▷ (dom (gset loc) γ = dom (gset loc) g)
      ★ ▷ (own graph_name (● (Some (1%Qp, γ) : graphUR)))
      ★ ▷ ([★ map] l ↦ v ∈ delete x (of_base_graph g γ),
           ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                        ★ m ↦ (ND_to_heap v).1)
      ★ ▷ (∃ u, (of_base_graph g γ !! x = Some u)
                  ★ ∃ (m : loc), Mrk !! x = Some m ★ x ↦ (#m, (ND_to_heap u).2)
                                                 ★ m ↦ (ND_to_heap u).1)
      ★ ▷ Γρ(q, x [↦] w).
  Proof. by iIntros; iNext; iApply graph_open. Qed.

  Lemma graph_close g Mrk γ q x w
        (Hd : dom (gset loc) γ = dom (gset loc) g)
    :
      (own graph_name (● (Some (1%Qp, γ) : graphUR)))
        ★ ([★ map] l ↦ v ∈ delete x (of_base_graph g γ),
           ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2) ★
                                        m ↦ (ND_to_heap v).1)
        ★ (∃ u, (of_base_graph g γ !! x = Some u)
                  ★ ∃ (m : loc), Mrk !! x = Some m ★ x ↦ (#m, (ND_to_heap u).2)
                                                 ★ m ↦ (ND_to_heap u).1)
        ★ Γρ(q, x [↦] w)
        ⊢ (own graph_name (● (Some (1%Qp, γ) : graphUR)))
        ★ ([★ map] l ↦ v ∈ (of_base_graph g γ),
           ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                        ★ m ↦ (ND_to_heap v).1)
        ★ Γρ(q, x [↦] w).
  Proof.
    iIntros "(Hg & Ha & Hl1 &Hl2)". rewrite own_graph_eq /own_graph_def.
    iCombine "Hg" "Hl2" as "Hg". iDestruct (@own_valid with "#Hg") as %Hvalid.
    iDestruct "Hg" as "[Hg Hl2]".
    iDestruct (auth_own_graph_valid with "Hg") as "[Hg %]". iFrame "Hg Hl2".
    assert (Hid : x ∈ dom (gset _) (of_base_graph g γ)).
    { rewrite of_base_graph_dom; auto. rewrite -Hd.
      eapply auth_subgraph; eauto; by rewrite dom_singleton elem_of_singleton.
    } revert Hid; rewrite elem_of_dom /is_Some. intros [y Hy].
    rewrite -{3}(insert_id _ _ _ Hy) -insert_delete.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
    iFrame "Ha". iDestruct "Hl1" as (u) "[Hu Hl1]". iDestruct "Hu" as %Hu.
      by rewrite Hy in Hu; inversion Hu; subst.
  Qed.

End graph.