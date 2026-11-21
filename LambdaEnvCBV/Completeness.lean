import LambdaEnvCBV.Typing
import LambdaEnvCBV.Uniform

/-!
# Completeness: `CFN M → Typ M`

Port of `Completeness.thy`.  σ-expansion (replacing a subterm by one with at least the same
typings), refinement of the top-level context (needed because a β_v-step requires its argument
to have an essential type), β_v-expansion, and subject expansion for `→v`.

Adaptations: `M →v N` is `cbv M N`, `M →v* N` is `Star cbv M N`.
-/

namespace LambdaEnvCBV

open Trm Ty

/-! ## σ-expansion: replacing a subterm by one with at least the same typings -/

def at_least (M N : Trm) : Prop := ∀ C A, Hasty C N A → Hasty C M A

theorem rep_AppL_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = app N L → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (app M L) A := by
  induction h with
  | TApp h1 h2 he _ _ => intro e hy; cases e; exact .TApp (hy _ _ h1) h2 he
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_AppL {M N : Trm} (L : Trm) (h : at_least M N) :
    at_least (app M L) (app N L) :=
  fun _ _ ht => rep_AppL_aux ht rfl h

theorem rep_AppR_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = app L N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (app L M) A := by
  induction h with
  | TApp h1 h2 he _ _ => intro e hy; cases e; exact .TApp h1 (hy _ _ h2) he
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_AppR {M N : Trm} (L : Trm) (h : at_least M N) :
    at_least (app L M) (app L N) :=
  fun _ _ ht => rep_AppR_aux ht rfl h

theorem rep_Lam_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N : Trm} {x : Var} :
    P = lam x N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (lam x M) A := by
  induction h with
  | TLam h1 h2 _ => intro e hy; cases e; exact .TLam h1 (hy _ _ h2)
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_Lam {M N : Trm} (x : Var) (h : at_least M N) : at_least (lam x M) (lam x N) :=
  fun _ _ ht => rep_Lam_aux ht rfl h

theorem rep_CompL_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = comp N L → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (comp M L) A := by
  induction h with
  | TComp h1 h2 _ _ => intro e hy; cases e; exact .TComp h1 (hy _ _ h2)
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_CompL {M N : Trm} (L : Trm) (h : at_least M N) :
    at_least (comp M L) (comp N L) :=
  fun _ _ ht => rep_CompL_aux ht rfl h

theorem rep_CompR_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} :
    P = comp L N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (comp L M) A := by
  induction h with
  | TComp h1 h2 _ _ => intro e hy; cases e; exact .TComp (hy _ _ h1) h2
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_CompR {M N : Trm} (L : Trm) (h : at_least M N) :
    at_least (comp L M) (comp L N) :=
  fun _ _ ht => rep_CompR_aux ht rfl h

theorem rep_ExtnL_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} {x : Var} :
    P = extn N x L → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (extn M x L) A := by
  induction h with
  | TExtn h1 h2 _ _ => intro e hy; cases e; exact .TExtn (hy _ _ h1) h2
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_ExtnL {M N : Trm} (x : Var) (L : Trm) (h : at_least M N) :
    at_least (extn M x L) (extn N x L) :=
  fun _ _ ht => rep_ExtnL_aux ht rfl h

theorem rep_ExtnR_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M N L : Trm} {x : Var} :
    P = extn L x N → (∀ C A, Hasty C N A → Hasty C M A) → Hasty C (extn L x M) A := by
  induction h with
  | TExtn h1 h2 _ _ => intro e hy; cases e; exact .TExtn h1 (hy _ _ h2)
  | TOm => intro _ _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e hy; exact .TInter (ih1 e hy) (ih2 e hy)
  | TSub _ h2 ih => intro e hy; exact .TSub (ih e hy) h2
  | _ => intro e; cases e

theorem rep_ExtnR {M N : Trm} (L : Trm) (x : Var) (h : at_least M N) :
    at_least (extn L x M) (extn L x N) :=
  fun _ _ ht => rep_ExtnR_aux ht rfl h

/-! ## Root rules -/

theorem exp_Ass (L M N : Trm) : at_least (comp (comp L M) N) (comp L (comp M N)) := by
  intro C A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  obtain ⟨D', h3, h4⟩ := gen_Comp h1 rfl
  exact .TComp h3 (.TComp h4 h2)

theorem exp_IdL (M : Trm) : at_least (comp iden M) M :=
  fun _ _ h => .TComp h (.TId _)

theorem exp_IdR (M : Trm) : at_least (comp M iden) M :=
  fun _ _ h => .TComp (.TId _) h

theorem exp_VarRef (x : Var) (M N : Trm) : at_least (comp (var x) (extn M x N)) M := by
  intro C A h
  have h1 : Hasty C (extn M x N) (Env ((x, A) :: []) false) := .TExtn h (typ_env_om _ _)
  have h2 : Hasty (Env [(x, A)] false) (var x) A := .TVar (.s_refl _) (map_of_cons_self _ _ _)
  exact .TComp h1 h2

theorem exp_VarSkip {x y : Var} (M N : Trm) (xy : x ≠ y) :
    at_least (comp (var y) (extn M x N)) (comp (var y) N) := by
  intro C A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  rcases gen_Var h2 rfl with h3 | ⟨m, ob, B, d, l, b⟩
  · exact .TSub (.TOm _ _) h3
  · have h4 : Hasty C N (Env m ob) := .TSub h1 d
    have h5 : Hasty C (extn M x N) (Env ((x, Om) :: m) ob) := .TExtn (.TOm _ _) h4
    have h6 : Hasty (Env ((x, Om) :: m) ob) (var y) A :=
      .TSub (.TVar (.s_refl _) (by rw [map_of_cons_ne _ _ xy]; exact l)) b
    exact .TComp h5 h6

theorem exp_DExtn (L : Trm) (x : Var) (M N : Trm) :
    at_least (comp (extn L x M) N) (extn (comp L N) x (comp M N)) := by
  intro C A h
  obtain ⟨B, m, ob, h1, h2, s⟩ := gen_Extn h rfl
  obtain ⟨D1, a1, a2⟩ := gen_Comp h1 rfl
  obtain ⟨D2, b1, b2⟩ := gen_Comp h2 rfl
  have h3 : Hasty C N (Ty.Inter D1 D2) := .TInter a1 b1
  have h4 : Hasty (Ty.Inter D1 D2) (extn L x M) (Env ((x, B) :: m) ob) :=
    .TExtn (narrowing a2 (.s_il _ _)) (narrowing b2 (.s_ir _ _))
  exact .TSub (.TComp h3 h4) s

theorem exp_DApp_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A) {M1 M2 N : Trm} :
    P = app (comp M1 N) (comp M2 N) → Hasty C (comp (app M1 M2) N) A := by
  induction h with
  | TApp p q he _ _ =>
    intro e; cases e
    obtain ⟨D1, a1, a2⟩ := gen_Comp p rfl
    obtain ⟨D2, b1, b2⟩ := gen_Comp q rfl
    exact .TComp (.TInter a1 b1)
      (.TApp (narrowing a2 (.s_il _ _)) (narrowing b2 (.s_ir _ _)) he)
  | TOm => intro _; exact .TOm _ _
  | TInter _ _ ih1 ih2 => intro e; exact .TInter (ih1 e) (ih2 e)
  | TSub _ h2 ih => intro e; exact .TSub (ih e) h2
  | _ => intro e; cases e

theorem exp_DApp (M1 M2 N : Trm) :
    at_least (comp (app M1 M2) N) (app (comp M1 N) (comp M2 N)) :=
  fun _ _ h => exp_DApp_aux h rfl

/-! ## Subject expansion for σ -/

theorem sig_expansion {M N : Trm} (h : Sig M N) : at_least M N := by
  induction h with
  | Ass L M N => exact exp_Ass L M N
  | IdL M => exact exp_IdL M
  | IdR M => exact exp_IdR M
  | DExtn L x M N => exact exp_DExtn L x M N
  | VarRef x M N => exact exp_VarRef x M N
  | VarSkip M N hxy => exact exp_VarSkip M N hxy
  | DApp M1 M2 N => exact exp_DApp M1 M2 N
  | AppL L _ ih => exact rep_AppL L ih
  | AppR L _ ih => exact rep_AppR L ih
  | Lam x _ ih => exact rep_Lam x ih
  | CompL L _ ih => exact rep_CompL L ih
  | CompR L _ ih => exact rep_CompR L ih
  | ExtnL x L _ ih => exact rep_ExtnL x L ih
  | ExtnR L x _ ih => exact rep_ExtnR L x ih

theorem subject_expansion_sig {M N : Trm} {C A : Ty} (h : Sig M N) (t : Hasty C N A) :
    Hasty C M A := sig_expansion h C A t

/-! ## Refining the top-level context

A β_v-step needs its argument to have an essential type.  For an inert argument this is
obtained by giving its head variable a suitable type in the top-level context.  Since β_v only
works at positions in the top-level context, refining the top-level context suffices. -/

theorem emeet_sub1 (m1 m2 : List (Var × Ty)) (ob : Bool) :
    Env (emeet m1 m2) ob ≼ Env m1 ob := by
  apply Sub.s_env
  · intro y A' hy
    rw [map_of_emeet, hy]
    cases h2 : map_of m2 y with
    | none => exact ⟨_, rfl, .s_refl _⟩
    | some B => exact ⟨_, rfl, .s_il _ _⟩
  · exact id

theorem emeet_sub2 (m1 m2 : List (Var × Ty)) (ob : Bool) :
    Env (emeet m1 m2) ob ≼ Env m2 ob := by
  apply Sub.s_env
  · intro y A' hy
    rw [map_of_emeet]
    cases h1 : map_of m1 y with
    | none => exact ⟨_, hy, .s_refl _⟩
    | some B => rw [hy]; exact ⟨_, rfl, .s_ir _ _⟩
  · exact id

theorem sub_env_head {B B' : Ty} (h : B ≼ B') (x : Var) (m : List (Var × Ty)) (ob : Bool) :
    Env ((x, B) :: m) ob ≼ Env ((x, B') :: m) ob := by
  apply Sub.s_env
  · intro y A' hy
    by_cases hx : x = y
    · subst hx
      rw [map_of_cons_self] at hy; cases hy
      exact ⟨_, map_of_cons_self _ _ _, h⟩
    · rw [map_of_cons_ne _ _ hx] at hy
      exact ⟨_, by rw [map_of_cons_ne _ _ hx]; exact hy, .s_refl _⟩
  · exact id

def exp_top (M N : Trm) : Prop :=
  ∀ m ob A, Hasty (Env m ob) N A → ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) M A

theorem exp_topI {M N : Trm}
    (h : ∀ m ob A, Hasty (Env m ob) N A → ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) M A) :
    exp_top M N := h

theorem exp_topD {M N : Trm} (h : exp_top M N) {m : List (Var × Ty)} {ob : Bool} {A : Ty}
    (t : Hasty (Env m ob) N A) : ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) M A :=
  h m ob A t

theorem refine_meet {m1 m m2 : List (Var × Ty)} {ob : Bool} {M : Trm} {A B : Ty}
    (s1 : Env m1 ob ≼ Env m ob) (t1 : Hasty (Env m1 ob) M A)
    (s2 : Env m2 ob ≼ Env m ob) (t2 : Hasty (Env m2 ob) M B) :
    ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) M (Inter A B) := by
  have h1 : Hasty (Env (emeet m1 m2) ob) M A := narrowing t1 (emeet_sub1 _ _ _)
  have h2 : Hasty (Env (emeet m1 m2) ob) M B := narrowing t2 (emeet_sub2 _ _ _)
  exact ⟨_, .s_trans (emeet_sub1 _ _ _) s1, .TInter h1 h2⟩

theorem rep_AppL_top_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A)
    {M N L : Trm} {m : List (Var × Ty)} {ob : Bool} :
    P = app N L → C = Env m ob → exp_top M N →
      ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) (app M L) A := by
  induction h with
  | TApp h1 h2 he _ _ =>
    intro e hC hx; cases e; subst hC
    obtain ⟨m', s, t⟩ := exp_topD hx h1
    exact ⟨m', s, .TApp t (narrowing h2 s) he⟩
  | TOm => intro _ hC _; subst hC; exact ⟨m, .s_refl _, .TOm _ _⟩
  | TInter _ _ ih1 ih2 =>
    intro e hC hx
    obtain ⟨m1, s1, t1⟩ := ih1 e hC hx
    obtain ⟨m2, s2, t2⟩ := ih2 e hC hx
    exact refine_meet s1 t1 s2 t2
  | TSub _ h2 ih =>
    intro e hC hx
    obtain ⟨m', s, t⟩ := ih e hC hx
    exact ⟨m', s, .TSub t h2⟩
  | _ => intro e _ _; cases e

theorem rep_AppL_top {M N : Trm} (L : Trm) (h : exp_top M N) : exp_top (app M L) (app N L) :=
  fun _ _ _ t => rep_AppL_top_aux t rfl rfl h

theorem rep_AppR_top_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A)
    {M N L : Trm} {m : List (Var × Ty)} {ob : Bool} :
    P = app L N → C = Env m ob → exp_top M N →
      ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) (app L M) A := by
  induction h with
  | TApp h1 h2 he _ _ =>
    intro e hC hx; cases e; subst hC
    obtain ⟨m', s, t⟩ := exp_topD hx h2
    exact ⟨m', s, .TApp (narrowing h1 s) t he⟩
  | TOm => intro _ hC _; subst hC; exact ⟨m, .s_refl _, .TOm _ _⟩
  | TInter _ _ ih1 ih2 =>
    intro e hC hx
    obtain ⟨m1, s1, t1⟩ := ih1 e hC hx
    obtain ⟨m2, s2, t2⟩ := ih2 e hC hx
    exact refine_meet s1 t1 s2 t2
  | TSub _ h2 ih =>
    intro e hC hx
    obtain ⟨m', s, t⟩ := ih e hC hx
    exact ⟨m', s, .TSub t h2⟩
  | _ => intro e _ _; cases e

theorem rep_AppR_top {M N : Trm} (L : Trm) (h : exp_top M N) : exp_top (app L M) (app L N) :=
  fun _ _ _ t => rep_AppR_top_aux t rfl rfl h

theorem rep_VarR_top_aux {C : Ty} {P : Trm} {A : Ty} (h : Hasty C P A)
    {M N : Trm} {x : Var} {m : List (Var × Ty)} {ob : Bool} :
    P = comp (var x) N → C = Env m ob → exp_top M N →
      ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) (comp (var x) M) A := by
  induction h with
  | TComp h1 h2 _ _ =>
    intro e hC hx; cases e; subst hC
    obtain ⟨m', s, t⟩ := exp_topD hx h1
    exact ⟨m', s, .TComp t h2⟩
  | TOm => intro _ hC _; subst hC; exact ⟨m, .s_refl _, .TOm _ _⟩
  | TInter _ _ ih1 ih2 =>
    intro e hC hx
    obtain ⟨m1, s1, t1⟩ := ih1 e hC hx
    obtain ⟨m2, s2, t2⟩ := ih2 e hC hx
    exact refine_meet s1 t1 s2 t2
  | TSub _ h2 ih =>
    intro e hC hx
    obtain ⟨m', s, t⟩ := ih e hC hx
    exact ⟨m', s, .TSub t h2⟩
  | _ => intro e _ _; cases e

theorem rep_VarR_top {M N : Trm} (x : Var) (h : exp_top M N) :
    exp_top (comp (var x) M) (comp (var x) N) :=
  fun _ _ _ t => rep_VarR_top_aux t rfl rfl h

/-! ## Fireballs have essential types -/

theorem lam_typable {C : Ty} {m : List (Var × Ty)} {ob : Bool} (x : Var) (M : Trm)
    (h : C ≼ Env m ob) : Hasty C (lam x M) (Arr Om Om) :=
  .TLam h (.TOm _ _)

theorem emeet_single_lookup (m : List (Var × Ty)) (x : Var) (A : Ty) :
    ∃ B, map_of (emeet m [(x, A)]) x = some B ∧ B ≼ A := by
  rw [map_of_emeet]
  cases h : map_of m x with
  | none => exact ⟨A, by simp [map_of], .s_refl _⟩
  | some A1 => exact ⟨Inter A1 A, by simp [map_of], .s_ir _ _⟩

theorem emeet_nonempty (m : List (Var × Ty)) (x : Var) (A : Ty) : emeet m [(x, A)] ≠ [] := by
  simp [emeet]

theorem inert_fb_typable_top (M : Trm) :
    (inert M → ∀ m ob A, ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) M A) ∧
    (fb M → ∀ m ob, ∃ m' T, Env m' ob ≼ Env m ob ∧ ess T ∧ Hasty (Env m' ob) M T) := by
  have F_of_I : ∀ M : Trm, (inert M → ∀ m ob A, ∃ m', Env m' ob ≼ Env m ob ∧
        Hasty (Env m' ob) M A) →
      inert M → ∀ m ob, ∃ m' T, Env m' ob ≼ Env m ob ∧ ess T ∧ Hasty (Env m' ob) M T := by
    intro M hi h m ob
    obtain ⟨m', s, t⟩ := hi h m ob (TV 0)
    exact ⟨m', TV 0, s, by simp [ess], t⟩
  induction M with
  | var x =>
    have i : inert (var x) → ∀ m ob A, ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) (var x) A := by
      intro _ m ob A
      obtain ⟨B, l, b⟩ := emeet_single_lookup m x A
      exact ⟨_, emeet_sub1 _ _ _, .TSub (.TVar (.s_refl _) l) b⟩
    exact ⟨i, fun _ => F_of_I _ i (.IVar x)⟩
  | lam x M _ =>
    refine ⟨fun h => absurd h (not_inert_Lam _ _), fun _ m ob => ?_⟩
    exact ⟨m, Arr Om Om, .s_refl _, by simp [ess], lam_typable x M (.s_refl _)⟩
  | app M1 M2 ih1 ih2 =>
    have i : inert (app M1 M2) → ∀ m ob A, ∃ m', Env m' ob ≼ Env m ob ∧
        Hasty (Env m' ob) (app M1 M2) A := by
      intro h m ob A
      obtain ⟨a1, a2⟩ := inert_App_iff.1 h
      obtain ⟨m1, T, s1, e, t1⟩ := ih2.2 a2 m ob
      obtain ⟨m2, s2, t2⟩ := ih1.1 a1 m1 ob (Arr T A)
      exact ⟨m2, .s_trans s2 s1, .TApp t2 (narrowing t1 s2) e⟩
    exact ⟨i, fun h => F_of_I _ i (inert_App_iff.2 (fb_App_iff.1 h))⟩
  | iden =>
    refine ⟨fun h => absurd h not_inert_Id, fun _ m ob => ?_⟩
    exact ⟨emeet m [(0, Om)], Env (emeet m [(0, Om)]) ob, emeet_sub1 _ _ _,
      Or.inl (emeet_nonempty _ _ _), .TId _⟩
  | extn M1 x M2 _ _ =>
    refine ⟨fun h => absurd h (not_inert_Extn _ _ _), fun _ m ob => ?_⟩
    exact ⟨m, Env [(x, Om)] false, .s_refl _, Or.inl (by simp),
      .TExtn (.TOm _ _) (typ_env_om _ _)⟩
  | comp M1 M2 ih1 ih2 =>
    have i : inert (comp M1 M2) → ∀ m ob A, ∃ m', Env m' ob ≼ Env m ob ∧
        Hasty (Env m' ob) (comp M1 M2) A := by
      intro h m ob A
      cases h with
      | IComp x a2 =>
        obtain ⟨m', s, t⟩ := ih2.1 a2 m ob (Env [(x, A)] true)
        exact ⟨m', s, .TComp t (.TVar (.s_refl _) (map_of_cons_self _ _ _))⟩
    refine ⟨i, fun h m ob => ?_⟩
    rcases fb_cases h with h | ⟨_, _, h⟩ | ⟨x, B, L, h'⟩ | h | ⟨_, _, _, h⟩
    · exact F_of_I _ i h m ob
    · cases h
    · cases h'
      exact ⟨m, Arr Om Om, .s_refl _, by simp [ess],
        .TComp (typ_env_om _ _) (lam_typable x B (.s_refl _))⟩
    · cases h
    · cases h

theorem fb_typable_top {M : Trm} (h : fb M) {m : List (Var × Ty)} {ob : Bool} :
    ∃ m' T, Env m' ob ≼ Env m ob ∧ ess T ∧ Hasty (Env m' ob) M T :=
  (inert_fb_typable_top M).2 h m ob

/-! ## β_v-expansion -/

theorem exp_Beta2_top {V : Trm} (f : fb V) (x : Var) (B : Trm) :
    exp_top (app (lam x B) V) (comp B (extn V x iden)) := by
  intro m ob A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  obtain ⟨T, m1, o1, v, i, s⟩ := gen_Extn h1 rfl
  have c : Env m ob ≼ Env m1 o1 := gen_Id i rfl
  obtain ⟨m', T', s', e, v'⟩ := fb_typable_top f (m := m) (ob := ob)
  have vv : Hasty (Env m' ob) V (Inter T T') := .TInter (narrowing v s') v'
  have s2 : Env ((x, Inter T T') :: m1) o1 ≼ D := .s_trans (sub_env_head (.s_il T T') _ _ _) s
  have h3 : Hasty (Env ((x, Inter T T') :: m1) o1) B A := narrowing h2 s2
  have h4 : Hasty (Env m' ob) (lam x B) (Arr (Inter T T') A) := .TLam (.s_trans s' c) h3
  exact ⟨m', s', .TApp h4 vv (Or.inr e)⟩

theorem exp_Beta1_top {V : Trm} (f : fb V) (x : Var) (B L : Trm) :
    exp_top (app (comp (lam x B) L) V) (comp B (extn V x L)) := by
  intro m ob A h
  obtain ⟨D, h1, h2⟩ := gen_Comp h rfl
  obtain ⟨T, m1, o1, v, l, s⟩ := gen_Extn h1 rfl
  obtain ⟨m', T', s', e, v'⟩ := fb_typable_top f (m := m) (ob := ob)
  have vv : Hasty (Env m' ob) V (Inter T T') := .TInter (narrowing v s') v'
  have s2 : Env ((x, Inter T T') :: m1) o1 ≼ D := .s_trans (sub_env_head (.s_il T T') _ _ _) s
  have h3 : Hasty (Env ((x, Inter T T') :: m1) o1) B A := narrowing h2 s2
  have h4 : Hasty (Env m1 o1) (lam x B) (Arr (Inter T T') A) := .TLam (.s_refl _) h3
  have h5 : Hasty (Env m' ob) (comp (lam x B) L) (Arr (Inter T T') A) :=
    .TComp (narrowing l s') h4
  exact ⟨m', s', .TApp h5 vv (Or.inr e)⟩

theorem beta_expansion_top {M N : Trm} (h : beta M N) : exp_top M N := by
  induction h with
  | @Beta1 N x M L hf => exact exp_Beta1_top hf x M L
  | @Beta2 N x M hf => exact exp_Beta2_top hf x M
  | @AppL M N L _ ih => exact rep_AppL_top L ih
  | @AppR L M N _ _ ih => exact rep_AppR_top L ih
  | @VarR M N x _ ih => exact rep_VarR_top x ih

/-! ## Subject expansion and completeness -/

theorem subject_expansion_top {M N : Trm} (s : cbv M N) {m : List (Var × Ty)} {ob : Bool}
    {A : Ty} (t : Hasty (Env m ob) N A) :
    ∃ m', Env m' ob ≼ Env m ob ∧ Hasty (Env m' ob) M A := by
  rcases s with s | s
  · exact ⟨m, .s_refl _, subject_expansion_sig s t⟩
  · exact exp_topD (beta_expansion_top s) t

theorem subject_expansion_steps {M N : Trm} (r : Star cbv M N) :
    ∀ {m : List (Var × Ty)} {ob : Bool} {A : Ty}, Hasty (Env m ob) N A →
      ∃ m', Hasty (Env m' ob) M A := by
  induction r with
  | refl => intro m ob A t; exact ⟨m, t⟩
  | step s _ ih =>
    intro m ob A t
    obtain ⟨m1, t1⟩ := ih t
    obtain ⟨m2, _, t2⟩ := subject_expansion_top s t1
    exact ⟨m2, t2⟩

theorem fb_Typ {M : Trm} (h : fb M) : Typ M := by
  obtain ⟨m', T, _, e, t⟩ := fb_typable_top h (m := []) (ob := true)
  exact ⟨m', true, T, t, e⟩

theorem completeness {M : Trm} (h : CFN M) : Typ M := by
  obtain ⟨N, r, _, c⟩ := h
  obtain ⟨m, T, _, e, t⟩ := fb_typable_top c (m := []) (ob := true)
  obtain ⟨m', t'⟩ := subject_expansion_steps r t
  exact ⟨m', true, T, t', e⟩

end LambdaEnvCBV
