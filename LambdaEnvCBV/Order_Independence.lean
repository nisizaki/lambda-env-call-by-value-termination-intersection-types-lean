import LambdaEnvCBV.Main_Results

/-!
# Independence of the evaluation order

Port of `Order_Independence.thy`.

`betan` (β_n) is β_v without the left-to-right restriction: an argument may be evaluated
before the function part.  We show that typability also characterizes termination of
σ ∪ β_n: every reduction sequence, in any order, is finite and ends in a fireball.

Adaptations: `M →n N` is `betan M N`; `M →v N` is `cbv M N`; `rtranclp R` is `Star R`.
-/

namespace LambdaEnvCBV

open Trm

inductive betan : Trm → Trm → Prop where
  | Beta1 {N : Trm} (x : Var) (M L : Trm) : fb N →
      betan (app (comp (lam x M) L) N) (comp M (extn N x L))
  | Beta2 {N : Trm} (x : Var) (M : Trm) : fb N →
      betan (app (lam x M) N) (comp M (extn N x iden))
  | AppL {M N : Trm} (L : Trm) : betan M N → betan (app M L) (app N L)
  | AppR {M N : Trm} (L : Trm) : betan M N → betan (app L M) (app L N)
  | VarR {M N : Trm} (x : Var) : betan M N → betan (comp (var x) M) (comp (var x) N)

def cbvn (M N : Trm) : Prop := Sig M N ∨ betan M N

def CFSNn (M : Trm) : Prop :=
  SN_at cbvn M ∧ ∀ N, Star cbvn M N → normal cbvn N → fb N

theorem beta_imp_betan {M N : Trm} (h : beta M N) : betan M N := by
  induction h with
  | Beta1 x M L hf => exact .Beta1 x M L hf
  | Beta2 x M hf => exact .Beta2 x M hf
  | AppL L _ ih => exact .AppL L ih
  | AppR _ _ ih => exact .AppR _ ih
  | VarR x _ ih => exact .VarR x ih

theorem cbv_imp_cbvn {M N : Trm} (h : cbv M N) : cbvn M N := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (beta_imp_betan h)

theorem normal_cbvn_NF {N : Trm} (h : normal cbvn N) : NF N :=
  fun b hb => h b (cbv_imp_cbvn hb)

theorem inert_fb_no_betan (M : Trm) :
    (inert M → ∀ N, ¬ betan M N) ∧ (fb M → ∀ N, ¬ betan M N) := by
  induction M with
  | var x => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | lam x M _ => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | iden => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | extn M x L _ _ => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | app M1 M2 ih1 ih2 =>
    have i : inert (app M1 M2) → ∀ N, ¬ betan (app M1 M2) N := by
      intro h N b
      obtain ⟨a1, a2⟩ := inert_App_iff.1 h
      cases b with
      | Beta1 => exact inert_not_Clo a1 rfl
      | Beta2 => exact inert_not_Lam a1 rfl
      | AppL _ b => exact ih1.1 a1 _ b
      | AppR _ b => exact ih2.2 a2 _ b
    exact ⟨i, fun h => i (inert_App_iff.2 (fb_App_iff.1 h))⟩
  | comp M1 M2 ih1 ih2 =>
    have i : inert (comp M1 M2) → ∀ N, ¬ betan (comp M1 M2) N := by
      intro h N b
      cases h with
      | IComp x m2 =>
        cases b with
        | VarR _ b => exact ih2.1 m2 _ b
    refine ⟨i, fun h N b => ?_⟩
    rcases fb_cases h with h | ⟨_, _, h⟩ | ⟨x, B, L, h'⟩ | h | ⟨_, _, _, h⟩
    · exact i h N b
    · cases h
    · cases h'; cases b
    · cases h
    · cases h

theorem fb_no_betan {M N : Trm} (h : fb M) : ¬ betan M N := (inert_fb_no_betan M).2 h N

/-! ## Commutation with σ -/

theorem betan_sig_commute {M M2 M1 : Trm} (hb : betan M M2) (hs : Sig M M1) :
    ∃ M3, betan M1 M3 ∧ Star Sig M2 M3 := by
  induction hb generalizing M1 with
  | @Beta1 N x B K hf =>
    cases hs with
    | AppL _ h =>
      rcases Clo_sig_inv h with ⟨B', rfl, h2⟩ | ⟨K', rfl, h2⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, .Beta1 _ _ _ hf, ss1 (.CompL _ h2)⟩
      · exact ⟨_, .Beta1 _ _ _ hf, ss1 (.CompR _ (.ExtnR _ _ h2))⟩
      · exact ⟨_, .Beta2 _ _ hf, .refl _⟩
    | AppR _ h =>
      exact ⟨_, .Beta1 _ _ _ (sig_fb hf h), ss1 (.CompR _ (.ExtnL _ _ h))⟩
  | @Beta2 N x B hf =>
    cases hs with
    | AppL _ h =>
      obtain ⟨B', rfl, h2⟩ := Lam_sig_inv h
      exact ⟨_, .Beta2 _ _ hf, ss1 (.CompL _ h2)⟩
    | AppR _ h =>
      exact ⟨_, .Beta2 _ _ (sig_fb hf h), ss1 (.CompR _ (.ExtnL _ _ h))⟩
  | @AppL M M' L b ih =>
    cases hs with
    | AppL _ h =>
      obtain ⟨M3, h1, h2⟩ := ih h
      exact ⟨_, .AppL _ h1, sig_steps_lift (f := fun P => app P L) (fun _ _ h => .AppL L h) h2⟩
    | AppR _ h => exact ⟨_, .AppL _ b, ss1 (.AppR _ h)⟩
  | @AppR M M' L b ih =>
    cases hs with
    | AppL _ h => exact ⟨_, .AppR _ b, ss1 (.AppL _ h)⟩
    | AppR _ h =>
      obtain ⟨M3, h1, h2⟩ := ih h
      exact ⟨_, .AppR _ h1, sig_steps_lift (f := fun P => app L P) (fun _ _ h => .AppR L h) h2⟩
  | @VarR M M' x b ih =>
    cases hs with
    | IdR => exact nomatch b
    | VarRef => exact nomatch b
    | VarSkip _ _ _ => exact nomatch b
    | CompL _ h => exact nomatch h
    | CompR _ h =>
      obtain ⟨M3, h1, h2⟩ := ih h
      exact ⟨_, .VarR _ h1,
        sig_steps_lift (f := fun P => comp (var x) P) (fun _ _ h => .CompR _ h) h2⟩

theorem snf_betan {M M' : Trm} (hb : betan M M') :
    ∃ M3, betan (snf M) M3 ∧ Star Sig M' M3 := by
  have key : ∀ n, ∀ M M', tlength M = n → betan M M' →
      ∃ M3, betan (snf M) M3 ∧ Star Sig M' M3 := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro M M' hn hb
      by_cases h : sig_normal M
      · have : snf M = M := snf_unique (.refl _) h
        rw [this]; exact ⟨M', hb, .refl _⟩
      · have h := Classical.not_forall.1 h
        obtain ⟨M1, s⟩ := h
        replace s := Classical.not_not.1 s
        obtain ⟨M3', a1, a2⟩ := betan_sig_commute hb s
        have lt := sig_tlength_decrease s
        obtain ⟨M3, b1, b2⟩ := ih (tlength M1) (by omega) M1 M3' rfl a1
        rw [snf_steps (ss1 s)] at b1
        exact ⟨M3, b1, a2.trans b2⟩
  exact key _ M M' rfl hb

/-! ## Diamond with the left-to-right step -/

theorem Lam_no_betan {x : Var} {M N : Trm} (h : betan (lam x M) N) : False := by cases h
theorem Clo_no_betan {x : Var} {M L N : Trm} (h : betan (comp (lam x M) L) N) : False := by
  cases h

theorem diamond {M M' M1 : Trm} (h1 : betan M M') (h2 : beta M M1) :
    M' = M1 ∨ ∃ M12, betan M1 M12 ∧ beta M' M12 := by
  induction h1 generalizing M1 with
  | @Beta1 N x B L hf =>
    cases h2 with
    | Beta1 => exact .inl rfl
    | AppL _ b => exact (Clo_no_beta b).elim
    | AppR _ b => exact (fb_no_beta hf b).elim
  | @Beta2 N x B hf =>
    cases h2 with
    | Beta2 => exact .inl rfl
    | AppL _ b => exact (Lam_no_beta b).elim
    | AppR _ b => exact (fb_no_beta hf b).elim
  | @AppL M M' L b ih =>
    cases h2 with
    | Beta1 => exact (Clo_no_betan b).elim
    | Beta2 => exact (Lam_no_betan b).elim
    | AppL _ b' =>
      rcases ih b' with h | ⟨M12, c1, c2⟩
      · subst h; exact .inl rfl
      · exact .inr ⟨_, .AppL _ c1, .AppL _ c2⟩
    | AppR hf _ => exact (fb_no_betan hf b).elim
  | @AppR M M' L b ih =>
    cases h2 with
    | Beta1 _ _ _ hf => exact (fb_no_betan hf b).elim
    | Beta2 _ _ hf => exact (fb_no_betan hf b).elim
    | AppL _ b' => exact .inr ⟨_, .AppR _ b, .AppL _ b'⟩
    | AppR hf b' =>
      rcases ih b' with h | ⟨M12, c1, c2⟩
      · subst h; exact .inl rfl
      · exact .inr ⟨_, .AppR _ c1, .AppR hf c2⟩
  | @VarR M M' x b ih =>
    cases h2 with
    | VarR _ b' =>
      rcases ih b' with h | ⟨M12, c1, c2⟩
      · subst h; exact .inl rfl
      · exact .inr ⟨_, .VarR _ c1, .VarR _ c2⟩

/-! ## Every β_n-step shortens the deterministic chain -/

theorem cd_fwd_sig_steps' {M M' : Trm} {n : Nat} {E : Trm} (r : Star Sig M M') (c : cd M n E) :
    cd M' n E := by
  induction r with
  | refl => exact c
  | step s _ ih => exact ih (cd_fwd_sig s c)

theorem cd_back_sig_steps {M M' : Trm} {n : Nat} {E : Trm} (r : Star Sig M M') (c : cd M' n E) :
    cd M n E := by
  induction r with
  | refl => exact c
  | step s _ ih => exact cd_back_sig s (ih c)

theorem cd_snf_self {M : Trm} {n : Nat} {E : Trm} (c : cd M n E) : cd (snf M) n E :=
  cd_fwd_sig_steps' (snf_spec M).1 c

theorem cd_betan {M M' : Trm} {n : Nat} {E : Trm} (c : cd M n E) (hE : fb E)
    (b : betan M M') : ∃ m, m < n ∧ cd M' m E := by
  have key : ∀ n, ∀ M M', cd M n E → betan M M' → ∃ m, m < n ∧ cd M' m E := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro M M' c b
      obtain ⟨M3, b3, s⟩ := snf_betan b
      cases c with
      | cd0 _ _ => exact (fb_no_betan hE b3).elim
      | @cdS _ N1 k _ hb' c' =>
        rcases diamond b3 hb' with h | ⟨M12, n1, m3⟩
        · subst h
          exact ⟨k, by omega, cd_back_sig_steps s c'⟩
        · obtain ⟨m, hm, cm⟩ := ih k (by omega) N1 M12 c' n1
          exact ⟨m + 1, by omega, cd_back_sig_steps s (cd_back_beta m3 cm)⟩
  exact key n M M' c b

theorem cd_SNn {M : Trm} {n : Nat} {E : Trm} (c : cd M n E) (hE : fb E) : SN_at cbvn M := by
  have key : ∀ n, ∀ M, cd M n E → SN_at cbvn M := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n IHn =>
      have inner : ∀ t, ∀ M, tlength M = t → cd M n E → SN_at cbvn M := by
        intro t
        induction t using Nat.strongRecOn with
        | _ t IHt =>
          intro M ht hc
          refine SN_at.intro fun N hs => ?_
          rcases hs with hs | hs
          · exact IHt (tlength N) (by have := sig_tlength_decrease hs; omega) N rfl
              (cd_fwd_sig hs hc)
          · obtain ⟨m, hm, c'⟩ := cd_betan hc hE hs
            exact IHn m hm N c'
      exact fun M hc => inner _ M rfl hc
  exact key n M c

theorem cd_reach_n {M N : Trm} (r : Star cbvn M N) :
    ∀ {n E}, cd M n E → fb E → ∃ m, cd N m E := by
  induction r with
  | refl => intro n E c _; exact ⟨n, c⟩
  | step s _ ih =>
    intro n E c hE
    rcases s with s | s
    · exact ih (cd_fwd_sig s c) hE
    · obtain ⟨m, _, c'⟩ := cd_betan c hE s
      exact ih c' hE

theorem CFN_imp_CFSNn {M : Trm} (h : CFN M) : CFSNn M := by
  obtain ⟨E, r, n, f⟩ := h
  obtain ⟨k, c⟩ := steps_cd r n
  refine ⟨cd_SNn c f, fun N rn hn => ?_⟩
  obtain ⟨m, cm⟩ := cd_reach_n rn c f
  have := (cd_det (NF_cd (normal_cbvn_NF hn)) cm).2
  rw [this]; exact f

/-! ## Blocked terms

Terms that can never become fireballs, whatever the order of evaluation. -/

inductive blk : Trm → Prop where
  | BId (N : Trm) : blk (app iden N)
  | BExtn (P : Trm) (y : Var) (Q N : Trm) : blk (app (extn P y Q) N)
  | BL {L : Trm} (N : Trm) : blk L → blk (app L N)
  | BR {L N : Trm} : fb L → blk N → blk (app L N)
  | BLam (x y : Var) (B : Trm) : blk (comp (var x) (lam y B))
  | BClo (x y : Var) (B K : Trm) : blk (comp (var x) (comp (lam y B) K))
  | BComp {M : Trm} (x : Var) : blk M → blk (comp (var x) M)

theorem fb_Comp_Var_iff {x : Var} {M : Trm} : fb (comp (var x) M) ↔ inert M := by
  constructor
  · intro h
    cases h with
    | FInert h => cases h with | IComp _ h' => exact h'
  · intro h; exact .FInert (.IComp x h)

theorem blk_not_fb {M : Trm} (h : blk M) : ¬ fb M := by
  induction h with
  | BId N => intro h; exact not_inert_Id (fb_App_iff.1 h).1
  | BExtn P y Q N => intro h; exact not_inert_Extn _ _ _ (fb_App_iff.1 h).1
  | BL N _ ih => intro h; exact ih (.FInert (fb_App_iff.1 h).1)
  | BR _ _ ih => intro h; exact ih (fb_App_iff.1 h).2
  | BLam x y B => intro h; exact not_inert_Lam _ _ (fb_Comp_Var_iff.1 h)
  | BClo x y B K => intro h; exact not_inert_Clo _ _ _ (fb_Comp_Var_iff.1 h)
  | BComp x _ ih => intro h; exact ih (.FInert (fb_Comp_Var_iff.1 h))

theorem blk_shape {M : Trm} (h : blk M) :
    (∃ L N, M = app L N) ∨ (∃ x K, M = comp (var x) K) := by
  cases h with
  | BId => exact .inl ⟨_, _, rfl⟩
  | BExtn => exact .inl ⟨_, _, rfl⟩
  | BL => exact .inl ⟨_, _, rfl⟩
  | BR => exact .inl ⟨_, _, rfl⟩
  | BLam => exact .inr ⟨_, _, rfl⟩
  | BClo => exact .inr ⟨_, _, rfl⟩
  | BComp => exact .inr ⟨_, _, rfl⟩

theorem blk_step {M M' : Trm} (hb : blk M) (hs : cbvn M M') : blk M' := by
  induction hb generalizing M' with
  | BId N =>
    rcases hs with hs | hs
    · cases hs with
      | AppL _ h => exact (sig_Id_no _ h).elim
      | AppR _ _ => exact .BId _
    · cases hs with
      | AppL _ b => exact nomatch b
      | AppR _ _ => exact .BId _
  | BExtn P y Q N =>
    rcases hs with hs | hs
    · cases hs with
      | AppL _ h =>
        rcases inv_Extn h with ⟨A', _, rfl⟩ | ⟨B', _, rfl⟩ <;> exact .BExtn _ _ _ _
      | AppR _ _ => exact .BExtn _ _ _ _
    · cases hs with
      | AppL _ b => exact nomatch b
      | AppR _ _ => exact .BExtn _ _ _ _
  | @BL L N hL ih =>
    rcases hs with hs | hs
    · cases hs with
      | AppL _ h => exact .BL _ (ih (Or.inl h))
      | AppR _ _ => exact .BL _ hL
    · cases hs with
      | Beta1 =>
        rcases blk_shape hL with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> cases e
      | Beta2 =>
        rcases blk_shape hL with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> cases e
      | AppL _ b => exact .BL _ (ih (Or.inr b))
      | AppR _ _ => exact .BL _ hL
  | @BR L N hf hN ih =>
    rcases hs with hs | hs
    · cases hs with
      | AppL _ h => exact .BR (sig_fb hf h) hN
      | AppR _ h => exact .BR hf (ih (Or.inl h))
    · cases hs with
      | Beta1 _ _ _ hf' => exact (blk_not_fb hN hf').elim
      | Beta2 _ _ hf' => exact (blk_not_fb hN hf').elim
      | AppL _ b => exact (fb_no_betan hf b).elim
      | AppR _ b => exact .BR hf (ih (Or.inr b))
  | BLam x y B =>
    rcases hs with hs | hs
    · cases hs with
      | CompL _ h => exact (sig_Var_no _ _ h).elim
      | CompR _ h =>
        obtain ⟨B', rfl, _⟩ := Lam_sig_inv h
        exact .BLam _ _ _
    · cases hs with
      | VarR _ b => exact (Lam_no_betan b).elim
  | BClo x y B K =>
    rcases hs with hs | hs
    · cases hs with
      | CompL _ h => exact (sig_Var_no _ _ h).elim
      | CompR _ h =>
        rcases Clo_sig_inv h with ⟨B', rfl, _⟩ | ⟨K', rfl, _⟩ | ⟨rfl, rfl⟩
        · exact .BClo _ _ _ _
        · exact .BClo _ _ _ _
        · exact .BLam _ _ _
    · cases hs with
      | VarR _ b => exact (Clo_no_betan b).elim
  | @BComp M x hM ih =>
    rcases hs with hs | hs
    · cases hs with
      | IdR => rcases blk_shape hM with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> cases e
      | VarRef => rcases blk_shape hM with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> cases e
      | VarSkip _ _ _ => rcases blk_shape hM with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> cases e
      | CompL _ h => exact (sig_Var_no _ _ h).elim
      | CompR _ h => exact .BComp x (ih (Or.inl h))
    · cases hs with
      | VarR _ b => exact .BComp x (ih (Or.inr b))

theorem blk_steps {M N : Trm} (r : Star cbvn M N) (h : blk M) : blk N := by
  induction r with
  | refl => exact h
  | step s _ ih => exact ih (blk_step h s)

theorem NF_not_fb_blk (M : Trm) : NF M → ¬ fb M → blk M := by
  induction M with
  | var x => intro _ hc; exact absurd (fb_Var x) hc
  | lam x M _ => intro _ hc; exact absurd (.FLam x M) hc
  | iden => intro _ hc; exact absurd .FId hc
  | extn M x N _ _ => intro _ hc; exact absurd (.FExtn M x N) hc
  | app L N ihL ihN =>
    intro hN hc
    have nL : NF L := fun b hb => hN _ (cbv_AppL N hb)
    by_cases fL : fb L
    · have nN : NF N := fun b hb => hN _ (by
        rcases hb with h | h
        · exact Or.inl (.AppR L h)
        · exact Or.inr (.AppR fL h))
      by_cases fN : fb N
      · rcases fb_cases fL with h | ⟨x, B, h⟩ | ⟨x, B, K, h⟩ | h | ⟨P, y, Q, h⟩
        · exact absurd (fb_App_iff.2 ⟨h, fN⟩) hc
        · subst h; exact absurd (beta_imp_cbv (.Beta2 x B fN)) (hN _)
        · subst h; exact absurd (beta_imp_cbv (.Beta1 x B K fN)) (hN _)
        · subst h; exact .BId _
        · subst h; exact .BExtn _ _ _ _
      · exact .BR fL (ihN nN fN)
    · exact .BL _ (ihL nL fL)
  | comp M1 M2 ih1 ih2 =>
    intro hN hc
    have r : ∀ P, ¬ Sig (comp M1 M2) P := fun P h => hN P (Or.inl h)
    rcases M1 with x | ⟨x, B⟩ | ⟨P, Q⟩ | _ | ⟨P, y, Q⟩ | ⟨P, Q⟩
    · have n2 : NF M2 := fun b hb => hN _ (cbv_VarR x hb)
      by_cases f2 : fb M2
      · rcases fb_cases f2 with h | ⟨y, B, h⟩ | ⟨y, B, K, h⟩ | h | ⟨P, y, Q, h⟩
        · exact absurd (.FInert (.IComp x h)) hc
        · subst h; exact .BLam _ _ _
        · subst h; exact .BClo _ _ _ _
        · subst h; exact absurd (r _ (.IdR _)) id
        · subst h
          by_cases hyx : y = x
          · subst hyx; exact absurd (r _ (.VarRef _ _ _)) id
          · exact absurd (r _ (.VarSkip P Q hyx)) id
      · exact .BComp x (ih2 n2 f2)
    · exact absurd (.FClo x B M2) hc
    · exact absurd (r _ (.DApp P Q M2)) id
    · exact absurd (r _ (.IdL _)) id
    · exact absurd (r _ (.DExtn P y Q M2)) id
    · exact absurd (r _ (.Ass P Q M2)) id

theorem SN_at_mono {α : Type} {R S : α → α → Prop} {M : α} (h : SN_at R M)
    (hRS : ∀ a b, S a b → R a b) : SN_at S M := by
  refine SN_at.induct (P := fun M => SN_at S M) h ?_
  intro a _ ih
  exact SN_at.intro fun b hb => ih b (hRS _ _ hb)

theorem SN_normal_reach {α : Type} {R : α → α → Prop} {a : α} (h : SN_at R a) :
    ∃ b, Star R a b ∧ normal R b := by
  refine SN_at.induct (P := fun a => ∃ b, Star R a b ∧ normal R b) h ?_
  intro a _ ih
  by_cases hn : normal R a
  · exact ⟨a, .refl _, hn⟩
  · have hn := Classical.not_forall.1 hn
    obtain ⟨b, hb⟩ := hn
    replace hb := Classical.not_not.1 hb
    obtain ⟨c, r, n⟩ := ih b hb
    exact ⟨c, .step hb r, n⟩

theorem cbv_steps_cbvn {M N : Trm} (r : Star cbv M N) : Star cbvn M N :=
  steps_lift (f := fun P => P) (fun _ _ h => cbv_imp_cbvn h) r

theorem CFSNn_imp_CFN {M : Trm} (c : CFSNn M) : CFN M := by
  obtain ⟨sn, cf⟩ := c
  have sn' : SN_at cbv M := SN_at_mono sn (fun _ _ h => cbv_imp_cbvn h)
  obtain ⟨N, r, n⟩ := SN_normal_reach sn'
  have rn : Star cbvn M N := cbv_steps_cbvn r
  have fN : fb N := by
    refine Classical.byContradiction fun hf => ?_
    have b : blk N := NF_not_fb_blk N n hf
    have sN : SN_at cbvn N := sn.star rn
    obtain ⟨P, rp, np⟩ := SN_normal_reach sN
    have bP : blk P := blk_steps rp b
    exact blk_not_fb bP (cf P (rn.trans rp) np)
  exact ⟨N, r, n, fN⟩

theorem main_characterization_any_order {M : Trm} : Typ M ↔ CFSNn M :=
  ⟨fun h => CFN_imp_CFSNn (main_characterization.1 h),
   fun h => main_characterization.2 (CFSNn_imp_CFN h)⟩

end LambdaEnvCBV
