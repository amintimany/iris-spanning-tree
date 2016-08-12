From iris.heap_lang Require Export lifting heap.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre ghost_ownership tactics.
Import uPred.

Require Import iris_spanning_tree.graph.

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

  Definition marked_def (l : loc) : iPropG heap_lang Σ :=
    auth_own marking_name ({[ l := () ]} : markingUR).
  Definition marked_aux : { x | x = @marked_def }. by eexists. Qed.
  Definition marked := proj1_sig marked_aux.
  Definition marked_eq : @marked = @marked_def := proj2_sig marked_aux.

  Lemma dup_marking (m : markingUR) : m ≡ m ⋅ m.
  Proof.
    intros i. rewrite lookup_op.
    match goal with
      |- ?B ≡ ?A ⋅ ?A => change B with A; by destruct A as [[]|]
    end.
  Qed.

  Notation "'μ(' x )" := (marked x) (format "μ( x )").

  Lemma dup_marked l : μ(l) ⊣⊢ μ(l) ★ μ(l).
  Proof. by rewrite marked_eq /marked_def -auth_own_op -dup_marking. Qed.

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
    - by rewrite marked_eq /marked_def /auth_own own_op.
  Qed.

End marking_definitions.

Notation "'μ(' x )" := (marked x) (format "μ( x )").

(* Invariant token. This allows us to dispose the invariant. *)
Definition invtokN : namespace := nroot .@ "SPT_invtok".
Definition invtokUR : ucmraT := optionUR fracR.

(** The CMRA we need. *)
Class invtokG Σ := InvTokG {
  invtok_inG :> authG heap_lang Σ invtokUR;
  invtok_name : gname
}.
(** The Functor we need. *)
Definition invtokGF : gFunctor := authGF invtokUR.

Section invtok_definitions.
  Context `{Ii : invtokG Σ}.

  Definition token_def (q : Qp) : iPropG heap_lang Σ :=
    auth_own invtok_name (Some q).
  Definition token_aux : { x | x = @token_def }. by eexists. Qed.
  Definition token := proj1_sig token_aux.
  Definition token_eq : @token = @token_def := proj2_sig token_aux.

  Notation "'κ(' q )" := (token q) (format "κ( q )").

  Lemma token_exclusive q : κ(1) ★ κ(q) ⊢ False.
  Proof.
    iIntros "H".
    rewrite token_eq /token_def -auth_own_op.
    rewrite /auth_own own_valid. iDestruct "H" as %H.
    rewrite /op //= /cmra_op //= /ucmra_op //= in H.
    exfalso; eapply exclusive_l; [|exact H].
    typeclasses eauto.
  Qed.

  Definition packed_def P : iPropG heap_lang Σ := (κ(1) ∨ P)%I.
  Definition packed_aux : { x | x = @packed_def }. by eexists. Qed.
  Definition packed := proj1_sig packed_aux.
  Definition packed_eq : @packed = @packed_def := proj2_sig packed_aux.

  Notation "'ρκ(' P )" := (packed P) (format "ρκ( P )").

  Lemma unPack q P : κ(q) ★ ρκ(P) ⊢ P ★ κ(q).
  Proof.
    rewrite packed_eq /packed_def.
    iIntros "[H1 [H2|H2]]".
    - iExFalso; iApply token_exclusive; iSplitL "H2"; eauto.
    - iSplitL "H2"; trivial.
  Qed.

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

(* The graph monoid. *)
Definition graphN : namespace := nroot .@ "SPT_graph".
Definition graphUR : ucmraT :=
  optionUR
    (prodR fracR
           (gmapR
              loc
              (optionR (exclR (dec_agreeR (option loc * option loc)))))
    ).

(** The CMRA we need. *)
Class graphG Σ := GraphG {
  graph_inG :> authG heap_lang Σ graphUR;
  graph_name : gname
}.
(** The Functor we need. *)
Definition graphGF : gFunctor := authGF graphUR.

Definition to_graph (g : graph loc) : graphUR :=
  Some (1%Qp,
        fmap (λ v : bool * (option loc * option loc),
                    match v with
                    | (m, w) =>
                      if m then Some (Excl (DecAgree w)) else None
                    end
             ) g
       ).

Definition of_graph_elem (g : graph loc) i v
  : option (bool * (option loc * option loc)) :=
  match v with
  | None => g !! i
  | Some u => match u with
             | Excl (DecAgree w) => Some (true, w)
             | _ => None
             end
  end.

Definition of_graph (g : graph loc) (γ : graphUR) : graph loc :=
  match γ with
  | Some (_, δ) => (map_imap (of_graph_elem g) δ)
  | None => ∅
  end.

Section definitions.
  Context `{Ih : heapG Σ} `{Ig : graphG Σ}.

  Definition graph_inv (h : heapUR) : iPropG heap_lang Σ :=
    ownP (of_heap h).
  Definition heap_ctx : iPropG heap_lang Σ :=
    auth_ctx heap_name heapN heap_inv.

  Global Instance heap_inv_proper : Proper ((≡) ==> (⊣⊢)) heap_inv.
  Proof. solve_proper. Qed.
  Global Instance heap_ctx_persistent : PersistentP heap_ctx.
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque heap_ctx heap_mapsto.
Instance: Params (@heap_inv) 1.
Instance: Params (@heap_mapsto) 4.
Instance: Params (@heap_ctx) 2.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Section heap.
  Context {Σ : gFunctors}.
  Implicit Types P Q : iPropG heap_lang Σ.
  Implicit Types Φ : val → iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapUR.

  (** Conversion to heaps and back *)
  Global Instance of_heap_proper : Proper ((≡) ==> (=)) of_heap.
  Proof. solve_proper. Qed.
  Lemma from_to_heap σ : of_heap (to_heap σ) = σ.
  Proof.
    apply map_eq=>l. rewrite lookup_omap lookup_fmap. by case (σ !! l).
  Qed.
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma of_heap_insert l v h :
    of_heap (<[l:=(1%Qp, DecAgree v)]> h) = <[l:=v]> (of_heap h).
  Proof. by rewrite /of_heap -(omap_insert _ _ _ (1%Qp, DecAgree v)). Qed.
  Lemma of_heap_singleton_op l q v h :
    ✓ ({[l := (q, DecAgree v)]} ⋅ h) →
    of_heap ({[l := (q, DecAgree v)]} ⋅ h) = <[l:=v]> (of_heap h).
  Proof.
    intros Hv. apply map_eq=> l'; destruct (decide (l' = l)) as [->|].
    - move: (Hv l). rewrite /of_heap lookup_insert
        lookup_omap (lookup_op _ h) lookup_singleton.
      case _:(h !! l)=>[[q' [v'|]]|] //=; last by move=> [??].
      move=> [? /dec_agree_op_inv [->]]. by rewrite dec_agree_idemp.
    - rewrite /of_heap lookup_insert_ne // !lookup_omap.
      by rewrite (lookup_op _ h) lookup_singleton_ne // left_id_L.
  Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap -fmap_insert. Qed.
  Lemma of_heap_None h l : ✓ h → of_heap h !! l = None → h !! l = None.
  Proof.
    move=> /(_ l). rewrite /of_heap lookup_omap.
    by case: (h !! l)=> [[q [v|]]|] //=; destruct 1; auto.
  Qed.
  Lemma heap_store_valid l h v1 v2 :
    ✓ ({[l := (1%Qp, DecAgree v1)]} ⋅ h) →
    ✓ ({[l := (1%Qp, DecAgree v2)]} ⋅ h).
  Proof.
    intros Hv l'; move: (Hv l'). destruct (decide (l' = l)) as [->|].
    - rewrite !lookup_op !lookup_singleton.
      by case: (h !! l)=> [x|] // /Some_valid/exclusive_l.
    - by rewrite !lookup_op !lookup_singleton_ne.
  Qed.
  Hint Resolve heap_store_valid.

  (** Allocation *)
  Lemma heap_alloc E σ :
    authG heap_lang Σ heapUR → nclose heapN ⊆ E →
    ownP σ ={E}=> ∃ _ : heapG Σ, heap_ctx ∧ [★ map] l↦v ∈ σ, l ↦ v.
  Proof.
    intros. rewrite -{1}(from_to_heap σ). etrans.
    { rewrite [ownP _]later_intro.
      apply (auth_alloc (ownP ∘ of_heap) heapN E); auto using to_heap_valid. }
    apply pvs_mono, exist_elim=> γ.
    rewrite -(exist_intro (HeapG _ _ γ)) /heap_ctx; apply and_mono_r.
    rewrite heap_mapsto_eq /heap_mapsto_def /heap_name.
    induction σ as [|l v σ Hl IH] using map_ind.
    { rewrite big_sepM_empty; apply True_intro. }
    rewrite to_heap_insert big_sepM_insert //.
    rewrite (insert_singleton_op (to_heap σ));
      last by rewrite lookup_fmap Hl; auto.
    by rewrite auth_own_op IH.
  Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto *)
  Global Instance heap_mapsto_timeless l q v : TimelessP (l ↦{q} v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦{q1} v ★ l ↦{q2} v ⊣⊢ l ↦{q1+q2} v.
  Proof.
    by rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_idemp.
  Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦{q1} v1 ★ l ↦{q2} v2 ⊣⊢ v1 = v2 ∧ l ↦{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_equiv // left_id. }
    rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_ne //.
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite auth_own_valid gmap_validI (forall_elim l) lookup_singleton.
    rewrite option_validI prod_validI frac_validI discrete_valid.
    by apply pure_elim_r.
  Qed.

  Lemma heap_mapsto_op_split l q v : l ↦{q} v ⊣⊢ (l ↦{q/2} v ★ l ↦{q/2} v).
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

  (** Weakest precondition *)
  (* FIXME: try to reduce usage of wp_pvs. We're losing view shifts here. *)
  Lemma wp_alloc E e v Φ :
    to_val e = Some v → nclose heapN ⊆ E →
    heap_ctx ★ ▷ (∀ l, l ↦ v ={E}=★ Φ (LitV (LitLoc l))) ⊢ WP Alloc e @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val ?) "[#Hinv HΦ]". rewrite /heap_ctx.
    iPvs (auth_empty heap_name) as "Hheap".
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); eauto with fsaV.
    iFrame "Hinv Hheap". iIntros (h). rewrite left_id.
    iIntros "[% Hheap]". rewrite /heap_inv.
    iApply wp_alloc_pst. iFrame "Hheap". iNext.
    iIntros (l) "[% Hheap]"; iPvsIntro; iExists {[ l := (1%Qp, DecAgree v) ]}.
    rewrite -of_heap_insert -(insert_singleton_op h); last by apply of_heap_None.
    iFrame "Hheap". iSplitR; first iPureIntro.
    { by apply alloc_unit_singleton_local_update; first apply of_heap_None. }
    iIntros "Hheap". iApply "HΦ". by rewrite heap_mapsto_eq /heap_mapsto_def.
  Qed.

  Lemma wp_load E l q v Φ :
    nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦{q} v ★ ▷ (l ↦{q} v ={E}=★ Φ v)
    ⊢ WP Load (Lit (LitLoc l)) @ E {{ Φ }}.
  Proof.
    iIntros (?) "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); eauto with fsaV.
    iFrame "Hh Hl". iIntros (h) "[% Hl]". rewrite /heap_inv.
    iApply (wp_load_pst _ (<[l:=v]>(of_heap h)));first by rewrite lookup_insert.
    rewrite of_heap_singleton_op //. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists _; iSplit; first done.
    rewrite of_heap_singleton_op //. by iFrame.
  Qed.

  Lemma wp_store E l v' e v Φ :
    to_val e = Some v → nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦ v' ★ ▷ (l ↦ v ={E}=★ Φ (LitV LitUnit))
    ⊢ WP Store (Lit (LitLoc l)) e @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val ?) "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); eauto with fsaV.
    iFrame "Hh Hl". iIntros (h) "[% Hl]". rewrite /heap_inv.
    iApply (wp_store_pst _ (<[l:=v']>(of_heap h))); rewrite ?lookup_insert //.
    rewrite insert_insert !of_heap_singleton_op; eauto. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists {[l := (1%Qp, DecAgree v)]}; iSplit.
    { iPureIntro; by apply singleton_local_update, exclusive_local_update. }
    rewrite of_heap_singleton_op //; eauto. by iFrame.
  Qed.

  Lemma wp_cas_fail E l q v' e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦{q} v' ★ ▷ (l ↦{q} v' ={E}=★ Φ (LitV (LitBool false)))
    ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ??) "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); eauto with fsaV.
    iFrame "Hh Hl". iIntros (h) "[% Hl]". rewrite /heap_inv.
    iApply (wp_cas_fail_pst _ (<[l:=v']>(of_heap h))); rewrite ?lookup_insert //.
    rewrite of_heap_singleton_op //. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists _; iSplit; first done.
    rewrite of_heap_singleton_op //. by iFrame.
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose heapN ⊆ E →
    heap_ctx ★ ▷ l ↦ v1 ★ ▷ (l ↦ v2 ={E}=★ Φ (LitV (LitBool true)))
    ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ?) "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); eauto with fsaV.
    iFrame "Hh Hl". iIntros (h) "[% Hl]". rewrite /heap_inv.
    iApply (wp_cas_suc_pst _ (<[l:=v1]>(of_heap h))); rewrite ?lookup_insert //.
    rewrite insert_insert !of_heap_singleton_op; eauto. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists {[l := (1%Qp, DecAgree v2)]}; iSplit.
    { iPureIntro; by apply singleton_local_update, exclusive_local_update. }
    rewrite of_heap_singleton_op //; eauto. by iFrame.
  Qed.
End heap.