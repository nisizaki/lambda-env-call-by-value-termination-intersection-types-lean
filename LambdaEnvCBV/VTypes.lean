import LambdaEnvCBV.Lambda

/-!
# A classical call-by-value intersection-type system on de Bruijn terms

Port of `VTypes.thy`.

Types are built from type variables, a constant `ν`, arrows and intersections, ordered by the
usual subtyping (without arrow distributivity), with every type below `ν`.  As in the
call-by-value systems of Ronchi Della Rocca and Paolini, `ν` is given to abstractions by an axiom
(and to variables through the context); there is no rule giving a type to an arbitrary term.
It is an idempotent counterpart of Ehrhard's call-by-value multi types, used by Accattoli and
Guerrieri for Open CBV.  Main result `classical_VN`: a term is normalizable in Open CBV (the
fireball calculus) iff it is typable.

Adaptations: Isabelle sets of terms are predicates `dB → Prop` (`t ∈ vsem A` is `vsem A t`);
`A ≤ᵥ B` is `vsub A B`; `Γ ⊢ᵥ t : A` is `vty_of Γ t A`; `evals S` is a predicate transformer;
`rtranclp` is `Star`.
-/

namespace LambdaEnvCBV

open dB

inductive vty where
  | VTV : Nat → vty
  | VNu : vty
  | VArr : vty → vty → vty
  | VInter : vty → vty → vty

open vty

inductive vsub : vty → vty → Prop where
  | vs_refl (A : vty) : vsub A A
  | vs_trans {A B C : vty} : vsub A B → vsub B C → vsub A C
  | vs_nu (A : vty) : vsub A VNu
  | vs_inter1 (A B : vty) : vsub (VInter A B) A
  | vs_inter2 (A B : vty) : vsub (VInter A B) B
  | vs_glb {A B C : vty} : vsub A B → vsub A C → vsub A (VInter B C)
  | vs_arr {A' A B B' : vty} : vsub A' A → vsub B B' → vsub (VArr A B) (VArr A' B')

/-- Stream cons (`a ## f` in Isabelle). -/
def scons {α : Type} (a : α) (f : Nat → α) : Nat → α
  | 0 => a
  | j + 1 => f j

infixr:65 " ## " => scons

@[simp] theorem scons_0 {α : Type} (a : α) (f : Nat → α) : (a ## f) 0 = a := rfl

@[simp] theorem scons_Suc {α : Type} (a : α) (f : Nat → α) (j : Nat) : (a ## f) (j + 1) = f j := rfl

@[simp] theorem scons_comp_Suc {α : Type} (a : α) (f : Nat → α) : (a ## f) ∘ Nat.succ = f := rfl

theorem scons_eta {α : Type} (f : Nat → α) : (f 0 ## (fun i => f (i + 1))) = f := by
  funext i; cases i <;> rfl

inductive vty_of : (Nat → vty) → dB → vty → Prop where
  | vVar {Γ : Nat → vty} {i : Nat} {A : vty} : Γ i = A → vty_of Γ (DVar i) A
  | vAbs {A : vty} {Γ : Nat → vty} {t : dB} {B : vty} :
      vty_of (A ## Γ) t B → vty_of Γ (DAbs t) (VArr A B)
  | vApp {Γ : Nat → vty} {s : dB} {A B : vty} {u : dB} :
      vty_of Γ s (VArr A B) → vty_of Γ u A → vty_of Γ (DApp s u) B
  | vNu {Γ : Nat → vty} {t : dB} : vty_of Γ (DAbs t) VNu
  | vInter {Γ : Nat → vty} {t : dB} {A B : vty} :
      vty_of Γ t A → vty_of Γ t B → vty_of Γ t (VInter A B)
  | vSub {Γ : Nat → vty} {t : dB} {A B : vty} :
      vty_of Γ t A → vsub A B → vty_of Γ t B

/-! ### Renamings and simultaneous substitution -/

def rup (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => r j + 1

@[simp] theorem rup_0 (r : Nat → Nat) : rup r 0 = 0 := rfl
@[simp] theorem rup_Suc (r : Nat → Nat) (j : Nat) : rup r (j + 1) = r j + 1 := rfl

def dbren : dB → (Nat → Nat) → dB
  | DVar i, r => DVar (r i)
  | DApp s t, r => DApp (dbren s r) (dbren t r)
  | DAbs s, r => DAbs (dbren s (rup r))

def dbup (s : Nat → dB) : Nat → dB
  | 0 => DVar 0
  | j + 1 => dbren (s j) Nat.succ

@[simp] theorem dbup_0 (s : Nat → dB) : dbup s 0 = DVar 0 := rfl
@[simp] theorem dbup_Suc (s : Nat → dB) (j : Nat) : dbup s (j + 1) = dbren (s j) Nat.succ := rfl

def dbsub : dB → (Nat → dB) → dB
  | DVar i, s => s i
  | DApp t u, s => DApp (dbsub t s) (dbsub u s)
  | DAbs t, s => DAbs (dbsub t (dbup s))

@[simp] theorem dbren_Var (i : Nat) (r : Nat → Nat) : dbren (DVar i) r = DVar (r i) := rfl
@[simp] theorem dbren_App (s t : dB) (r : Nat → Nat) :
    dbren (DApp s t) r = DApp (dbren s r) (dbren t r) := rfl
@[simp] theorem dbren_Abs (s : dB) (r : Nat → Nat) : dbren (DAbs s) r = DAbs (dbren s (rup r)) := rfl
@[simp] theorem dbsub_Var (i : Nat) (s : Nat → dB) : dbsub (DVar i) s = s i := rfl
@[simp] theorem dbsub_App (t u : dB) (s : Nat → dB) :
    dbsub (DApp t u) s = DApp (dbsub t s) (dbsub u s) := rfl
@[simp] theorem dbsub_Abs (t : dB) (s : Nat → dB) : dbsub (DAbs t) s = DAbs (dbsub t (dbup s)) := rfl

theorem rup_comp (r' r : Nat → Nat) : rup r' ∘ rup r = rup (r' ∘ r) := by
  funext i; cases i <;> rfl

theorem ren_ren (t : dB) : ∀ (r r' : Nat → Nat), dbren (dbren t r) r' = dbren t (r' ∘ r) := by
  induction t with
  | DVar i => intro r r'; rfl
  | DApp a b iha ihb => intro r r'; simp [iha, ihb]
  | DAbs a ih => intro r r'; simp [ih, rup_comp]

theorem dbup_rup (s : Nat → dB) (r : Nat → Nat) : dbup s ∘ rup r = dbup (s ∘ r) := by
  funext i; cases i <;> rfl

theorem sub_ren (t : dB) : ∀ (r : Nat → Nat) (s : Nat → dB), dbsub (dbren t r) s = dbsub t (s ∘ r) := by
  induction t with
  | DVar i => intro r s; rfl
  | DApp a b iha ihb => intro r s; simp [iha, ihb]
  | DAbs a ih => intro r s; simp [ih, dbup_rup]

theorem ren_dbup (s : Nat → dB) (r : Nat → Nat) :
    (fun i => dbren (dbup s i) (rup r)) = dbup (fun i => dbren (s i) r) := by
  funext i
  cases i with
  | zero => rfl
  | succ j => simp only [dbup_Suc]; rw [ren_ren, ren_ren]; rfl

theorem ren_sub (t : dB) : ∀ (r : Nat → Nat) (s : Nat → dB),
    dbren (dbsub t s) r = dbsub t (fun i => dbren (s i) r) := by
  induction t with
  | DVar i => intro r s; rfl
  | DApp a b iha ihb => intro r s; simp [iha, ihb]
  | DAbs a ih => intro r s; simp [ih, ren_dbup]

theorem sub_dbup (s τ : Nat → dB) :
    (fun i => dbsub (dbup s i) (dbup τ)) = dbup (fun i => dbsub (s i) τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    simp only [dbup_Suc]
    rw [sub_ren, ren_sub]
    rfl

theorem sub_sub (t : dB) : ∀ (s τ : Nat → dB),
    dbsub (dbsub t s) τ = dbsub t (fun i => dbsub (s i) τ) := by
  induction t with
  | DVar i => intro s τ; rfl
  | DApp a b iha ihb => intro s τ; simp [iha, ihb]
  | DAbs a ih => intro s τ; simp [ih, sub_dbup]

theorem dbup_var : dbup DVar = DVar := by
  funext i; cases i <;> rfl

@[simp] theorem sub_var (t : dB) : dbsub t DVar = t := by
  induction t with
  | DVar i => rfl
  | DApp a b iha ihb => simp [iha, ihb]
  | DAbs a ih => simp [dbup_var, ih]

def dl (k : Nat) : Nat → Nat := fun i => if i < k then i else i + 1

@[simp] theorem dl_simp (k i : Nat) : dl k i = (if i < k then i else i + 1) := rfl

theorem rup_dl (k : Nat) : rup (dl k) = dl (k + 1) := by
  funext i
  cases i with
  | zero => simp [dl]
  | succ j => by_cases h : j < k <;> simp [h]

theorem lift_ren (t : dB) : ∀ k, lift t k = dbren t (dl k) := by
  induction t with
  | DVar i => intro k; by_cases h : i < k <;> simp [h]
  | DApp a b iha ihb => intro k; simp [iha, ihb]
  | DAbs a ih => intro k; simp [ih, rup_dl]

theorem dl_0 : dl 0 = Nat.succ := by
  funext i; simp

def ins (k : Nat) (u : dB) (i : Nat) : dB :=
  if i < k then DVar i else if i = k then u else DVar (i - 1)

theorem dbup_ins (k : Nat) (u : dB) : dbup (ins k u) = ins (k + 1) (lift u 0) := by
  funext i
  cases i with
  | zero => simp [ins]
  | succ j =>
    simp only [dbup_Suc]
    by_cases h1 : j < k
    · simp [ins, h1]
    · by_cases h2 : j = k
      · subst h2; simp [ins, lift_ren, dl_0]
      · have h3 : ¬ j + 1 < k + 1 := by omega
        have h4 : j + 1 ≠ k + 1 := by omega
        simp [ins, h1, h2, h3, h4]
        cases j with
        | zero => omega
        | succ j' => rfl

theorem subst_sub (t : dB) : ∀ (k : Nat) (u : dB), subst t u k = dbsub t (ins k u) := by
  induction t with
  | DVar i =>
    intro k u
    simp only [subst_Var, ins, dbsub_Var]
    by_cases h1 : k < i
    · have : ¬ i < k := by omega
      have : i ≠ k := by omega
      simp [h1, *]
    · by_cases h2 : i = k <;> simp [h1, h2] <;> omega
  | DApp a b iha ihb => intro k u; simp [iha, ihb]
  | DAbs a ih => intro k u; simp [ih, dbup_ins]

theorem lift_subst0 (s t : dB) (k : Nat) :
    lift (subst s t 0) k = subst (lift s (k + 1)) (lift t k) 0 := by
  have e : (fun i => dbren (ins 0 t i) (dl k)) = ins 0 (lift t k) ∘ dl (k + 1) := by
    funext i
    cases i with
    | zero => simp [ins, lift_ren]
    | succ j =>
      by_cases h : j < k
      · simp [ins, h]
      · simp [ins, h]
  rw [subst_sub, lift_ren, ren_sub, e, subst_sub, ← sub_ren]
  simp only [lift_ren]

theorem sub_up (t : dB) (σ : Nat → dB) (u : dB) :
    subst (dbsub t (dbup σ)) u 0 = dbsub t (u ## σ) := by
  have e : (fun i => dbsub (dbup σ i) (ins 0 u)) = (u ## σ) := by
    funext i
    cases i with
    | zero => simp [ins]
    | succ j =>
      have : ins 0 u ∘ Nat.succ = DVar := by funext i; simp [ins]
      simp only [dbup_Suc]
      rw [sub_ren, this, sub_var]; rfl
  rw [subst_sub, sub_sub, e]

/-! ### Facts about Open CBV -/

theorem vappL_star {s s' : dB} (h : Star vred s s') (t : dB) :
    Star vred (DApp s t) (DApp s' t) :=
  Star.map (fun s => DApp s t) (fun _ _ h => vred.vappL t h) h

theorem vappR_star {s t t' : dB} (hs : dfb s) (h : Star vred t t') :
    Star vred (DApp s t) (DApp s t') :=
  Star.map (fun t => DApp s t) (fun _ _ h => vred.vappR hs h) h

theorem normal_dfb {u : dB} : normal vred u → dfb u := by
  induction u with
  | DVar i => intro _; exact .fbInert (.inertVar i)
  | DAbs s _ => intro _; exact .fbAbs s
  | DApp s t ihs iht =>
    intro hn
    have fs : dfb s := ihs fun b h => hn _ (vred.vappL t h)
    have ft : dfb t := iht fun b h => hn _ (vred.vappR fs h)
    cases fs with
    | fbInert hi => exact .fbInert (.inertApp hi ft)
    | fbAbs s0 => exact absurd (vred.vbeta s0 ft) (hn _)

theorem vred_star_normal_unique {t u u' : dB} (h1 : Star vred t u) (h2 : Star vred t u')
    (n1 : normal vred u) (n2 : normal vred u') : u = u' := by
  induction h1 generalizing u' with
  | refl => exact (normal_star n1 h2).symm
  | step h _ ih =>
    cases h2 with
    | refl => exact absurd h (n2 _)
    | step h' r' => rw [vred_det h h'] at *; exact ih r' n1 n2

/-! ### Soundness: a realizability interpretation

A type denotes a set of fireballs; a term realizes a type when it evaluates to
a fireball in that set.  Inert terms belong to every type. -/

def evals (S : dB → Prop) (t : dB) : Prop := ∃ f, Star vred t f ∧ S f

def vsem : vty → dB → Prop
  | VTV _, f => dfb f
  | VNu, f => dfb f
  | VArr A B, f => dfb f ∧ ∀ g, vsem A g → evals (vsem B) (DApp f g)
  | VInter A B, f => vsem A f ∧ vsem B f

theorem vsem_dfb (A : vty) : ∀ {f : dB}, vsem A f → dfb f := by
  induction A with
  | VTV _ => intro f h; exact h
  | VNu => intro f h; exact h
  | VArr A B _ _ => intro f h; exact h.1
  | VInter A B iha _ => intro f h; exact iha h.1

theorem vsem_inert (A : vty) : ∀ {i : dB}, dinert i → vsem A i := by
  induction A with
  | VTV _ => intro i h; exact .fbInert h
  | VNu => intro i h; exact .fbInert h
  | VArr A B _ ihb =>
    intro i h
    refine ⟨.fbInert h, fun g hg => ⟨DApp i g, Star.refl _, ihb (.inertApp h (vsem_dfb A hg))⟩⟩
  | VInter A B iha ihb => intro i h; exact ⟨iha h, ihb h⟩

theorem vsem_sub {A B : vty} (h : vsub A B) : ∀ f, vsem A f → vsem B f := by
  induction h with
  | vs_refl => intro f m; exact m
  | vs_trans _ _ ih1 ih2 => intro f m; exact ih2 f (ih1 f m)
  | vs_nu A => intro f m; exact vsem_dfb A m
  | vs_inter1 => intro f m; exact m.1
  | vs_inter2 => intro f m; exact m.2
  | vs_glb _ _ ih1 ih2 => intro f m; exact ⟨ih1 f m, ih2 f m⟩
  | @vs_arr A' A B B' _ _ ih1 ih2 =>
    intro f m
    refine ⟨m.1, fun g hg => ?_⟩
    obtain ⟨h, r, hm⟩ := m.2 g (ih1 g hg)
    exact ⟨h, r, ih2 h hm⟩

theorem evals_inter {t : dB} {A B : vty} (h1 : evals (vsem A) t) (h2 : evals (vsem B) t) :
    evals (vsem (VInter A B)) t := by
  obtain ⟨f, rf, mf⟩ := h1
  obtain ⟨g, rg, mg⟩ := h2
  have nf := dfb_normal f |>.2 (vsem_dfb A mf)
  have ng := dfb_normal g |>.2 (vsem_dfb B mg)
  have := vred_star_normal_unique rf rg nf ng
  subst this
  exact ⟨f, rf, mf, mg⟩

theorem fund {Γ : Nat → vty} {t : dB} {A : vty} (h : vty_of Γ t A) :
    ∀ σ : Nat → dB, (∀ i, vsem (Γ i) (σ i)) → evals (vsem A) (dbsub t σ) := by
  induction h with
  | vVar e => intro σ hσ; subst e; exact ⟨σ _, Star.refl _, hσ _⟩
  | @vAbs A Γ t B _ ih =>
    intro σ hσ
    have : vsem (VArr A B) (DAbs (dbsub t (dbup σ))) := by
      refine ⟨.fbAbs _, fun g hg => ?_⟩
      have hs : ∀ i, vsem ((A ## Γ) i) ((g ## σ) i) := by
        intro i; cases i with
        | zero => exact hg
        | succ j => exact hσ j
      obtain ⟨f, r, m⟩ := ih _ hs
      refine ⟨f, Star.step ?_ r, m⟩
      have := vred.vbeta (dbsub t (dbup σ)) (vsem_dfb A hg)
      rwa [sub_up] at this
    exact ⟨_, Star.refl _, this⟩
  | vApp _ _ ih1 ih2 =>
    intro σ hσ
    obtain ⟨f, rf, mf⟩ := ih1 σ hσ
    obtain ⟨g, rg, mg⟩ := ih2 σ hσ
    obtain ⟨h, rh, mh⟩ := mf.2 g mg
    refine ⟨h, ?_, mh⟩
    exact ((vappL_star rf _).trans (vappR_star mf.1 rg)).trans rh
  | vNu => intro σ _; exact ⟨_, Star.refl _, .fbAbs _⟩
  | vInter _ _ ih1 ih2 => intro σ h; exact evals_inter (ih1 σ h) (ih2 σ h)
  | vSub _ hs ih =>
    intro σ h
    obtain ⟨f, r, m⟩ := ih σ h
    exact ⟨f, r, vsem_sub hs f m⟩

theorem classical_sound {Γ : Nat → vty} {t : dB} {A : vty} (h : vty_of Γ t A) : lam_VN t := by
  obtain ⟨f, r, m⟩ := fund h DVar (fun i => vsem_inert _ (.inertVar i))
  rw [sub_var] at r
  exact ⟨f, r, (dfb_normal f).2 (vsem_dfb A m)⟩

/-! ### Completeness: typing lemmas and subject expansion -/

def cle (Γ' Γ : Nat → vty) : Prop := ∀ i, vsub (Γ' i) (Γ i)

def cmeet (Γ1 Γ2 : Nat → vty) : Nat → vty := fun i => VInter (Γ1 i) (Γ2 i)

theorem cle_refl (Γ : Nat → vty) : cle Γ Γ := fun _ => vsub.vs_refl _

theorem cle_trans {Γ1 Γ2 Γ3 : Nat → vty} (h1 : cle Γ1 Γ2) (h2 : cle Γ2 Γ3) : cle Γ1 Γ3 :=
  fun i => vsub.vs_trans (h1 i) (h2 i)

theorem cle_meet1 (Γ1 Γ2 : Nat → vty) : cle (cmeet Γ1 Γ2) Γ1 := fun _ => vsub.vs_inter1 _ _

theorem cle_meet2 (Γ1 Γ2 : Nat → vty) : cle (cmeet Γ1 Γ2) Γ2 := fun _ => vsub.vs_inter2 _ _

theorem cle_glb {Γ Γ1 Γ2 : Nat → vty} (h1 : cle Γ Γ1) (h2 : cle Γ Γ2) : cle Γ (cmeet Γ1 Γ2) :=
  fun i => vsub.vs_glb (h1 i) (h2 i)

theorem gen_var_aux {Γ : Nat → vty} {r : dB} {C : vty} (h : vty_of Γ r C) :
    ∀ i, r = DVar i → vsub (Γ i) C := by
  induction h with
  | vVar e => intro i hi; cases hi; subst e; exact vsub.vs_refl _
  | vAbs _ _ => intro i hi; cases hi
  | vApp _ _ _ _ => intro i hi; cases hi
  | vNu => intro i hi; cases hi
  | vInter _ _ ih1 ih2 => intro i hi; exact vsub.vs_glb (ih1 i hi) (ih2 i hi)
  | vSub _ hs ih => intro i hi; exact vsub.vs_trans (ih i hi) hs

theorem gen_var {Γ : Nat → vty} {i : Nat} {C : vty} (h : vty_of Γ (DVar i) C) :
    vsub (Γ i) C := gen_var_aux h i rfl

theorem ctx_mono_aux {Γ : Nat → vty} {t : dB} {A : vty} (h : vty_of Γ t A) :
    ∀ Γ' : Nat → vty, (∀ i, vsub (Γ' i) (Γ i)) → vty_of Γ' t A := by
  induction h with
  | @vVar Γ i A e =>
    intro Γ' h
    subst e
    exact vty_of.vSub (vty_of.vVar rfl) (h i)
  | @vAbs A Γ t B _ ih =>
    intro Γ' h
    apply vty_of.vAbs
    apply ih
    intro i
    cases i with
    | zero => exact vsub.vs_refl _
    | succ j => exact h j
  | vApp _ _ ih1 ih2 => intro Γ' h; exact vty_of.vApp (ih1 Γ' h) (ih2 Γ' h)
  | vNu => intro Γ' _; exact vty_of.vNu
  | vInter _ _ ih1 ih2 => intro Γ' h; exact vty_of.vInter (ih1 Γ' h) (ih2 Γ' h)
  | vSub _ hs ih => intro Γ' h; exact vty_of.vSub (ih Γ' h) hs

theorem ctx_mono {Γ Γ' : Nat → vty} {t : dB} {A : vty} (h : vty_of Γ t A)
    (hs : cle Γ' Γ) : vty_of Γ' t A :=
  ctx_mono_aux h Γ' hs

theorem weaken_aux {Γ : Nat → vty} {t : dB} {A : vty} (h : vty_of Γ t A) :
    ∀ (ρ : Nat → Nat) (Γ' : Nat → vty), (∀ i, Γ' (ρ i) = Γ i) → vty_of Γ' (dbren t ρ) A := by
  induction h with
  | @vVar Γ i A e => intro ρ Γ' h; subst e; exact vty_of.vVar (h i)
  | @vAbs A Γ t B _ ih =>
    intro ρ Γ' h
    apply vty_of.vAbs
    apply ih
    intro i
    cases i with
    | zero => rfl
    | succ j => exact h j
  | vApp _ _ ih1 ih2 => intro ρ Γ' h; exact vty_of.vApp (ih1 ρ Γ' h) (ih2 ρ Γ' h)
  | vNu => intro ρ Γ' _; exact vty_of.vNu
  | vInter _ _ ih1 ih2 => intro ρ Γ' h; exact vty_of.vInter (ih1 ρ Γ' h) (ih2 ρ Γ' h)
  | vSub _ hs ih => intro ρ Γ' h; exact vty_of.vSub (ih ρ Γ' h) hs

theorem weaken {Γ Γ' : Nat → vty} {t : dB} {ρ : Nat → Nat} {A : vty} (h : vty_of Γ t A)
    (e : ∀ i, Γ' (ρ i) = Γ i) : vty_of Γ' (dbren t ρ) A :=
  weaken_aux h ρ Γ' e

theorem strengthen_aux {Γ : Nat → vty} {r : dB} {A : vty} (h : vty_of Γ r A) :
    ∀ (ρ : Nat → Nat) (t : dB), r = dbren t ρ → vty_of (Γ ∘ ρ) t A := by
  induction h with
  | @vVar Γ i A e =>
    intro ρ t hr
    cases t with
    | DVar j =>
      simp only [dbren_Var, dB.DVar.injEq] at hr
      subst hr; exact vty_of.vVar e
    | DApp _ _ => simp at hr
    | DAbs _ => simp at hr
  | @vAbs A Γ t B _ ih =>
    intro ρ s hr
    cases s with
    | DVar _ => simp at hr
    | DApp _ _ => simp at hr
    | DAbs s1 =>
      simp only [dbren_Abs, dB.DAbs.injEq] at hr
      have := ih (rup ρ) s1 hr
      have e : (A ## Γ) ∘ rup ρ = A ## (Γ ∘ ρ) := by funext i; cases i <;> rfl
      rw [e] at this
      exact vty_of.vAbs this
  | vApp _ _ ih1 ih2 =>
    intro ρ s hr
    cases s with
    | DVar _ => simp at hr
    | DAbs _ => simp at hr
    | DApp s1 s2 =>
      simp only [dbren_App, dB.DApp.injEq] at hr
      exact vty_of.vApp (ih1 ρ s1 hr.1) (ih2 ρ s2 hr.2)
  | vNu =>
    intro ρ s hr
    cases s with
    | DVar _ => simp at hr
    | DApp _ _ => simp at hr
    | DAbs _ => exact vty_of.vNu
  | vInter _ _ ih1 ih2 => intro ρ t hr; exact vty_of.vInter (ih1 ρ t hr) (ih2 ρ t hr)
  | vSub _ hs ih => intro ρ t hr; exact vty_of.vSub (ih ρ t hr) hs

theorem strengthen {Γ : Nat → vty} {t : dB} {ρ : Nat → Nat} {A : vty}
    (h : vty_of Γ (dbren t ρ) A) : vty_of (Γ ∘ ρ) t A :=
  strengthen_aux h ρ t rfl

/-- Inverting a substitution.  Every substituted term must already have type `ν`: this
replaces the CBN rule giving `ω` to every term, and it is where call-by-value differs
(only fireballs are substituted). -/
theorem expand_var {Γ : Nat → vty} {σ : Nat → dB} {j : Nat} {A : vty}
    (h : vty_of Γ (σ j) A) (nu : ∀ i, vty_of Γ (σ i) VNu) :
    ∃ Δ : Nat → vty, (∀ i, vty_of Γ (σ i) (Δ i)) ∧ vty_of Δ (DVar j) A := by
  refine ⟨fun k => if k = j then A else VNu, fun i => ?_, vty_of.vVar (by simp)⟩
  by_cases e : i = j
  · subst e; simpa using h
  · simpa [e] using nu i

theorem expand_aux {Γ : Nat → vty} {r : dB} {A : vty} (h : vty_of Γ r A) :
    ∀ (s : dB) (σ : Nat → dB), r = dbsub s σ → (∀ i, vty_of Γ (σ i) VNu) →
      ∃ Δ : Nat → vty, (∀ i, vty_of Γ (σ i) (Δ i)) ∧ vty_of Δ s A := by
  induction h with
  | @vVar Γ i A e =>
    intro s σ hr nu
    cases s with
    | DVar j =>
      have : σ j = DVar i := hr.symm
      exact expand_var (this ▸ vty_of.vVar e) nu
    | DApp _ _ => simp at hr
    | DAbs _ => simp at hr
  | @vAbs A Γ t B _ ih =>
    intro s σ hr nu
    cases s with
    | DVar j =>
      have : σ j = DAbs t := hr.symm
      exact expand_var (this ▸ vty_of.vAbs ‹_›) nu
    | DApp _ _ => simp at hr
    | DAbs s1 =>
      simp only [dbsub_Abs, dB.DAbs.injEq] at hr
      have nu' : ∀ i, vty_of (A ## Γ) (dbup σ i) VNu := by
        intro i
        cases i with
        | zero => exact vty_of.vSub (vty_of.vVar rfl) (vsub.vs_nu _)
        | succ j => exact weaken (ρ := Nat.succ) (Γ' := A ## Γ) (nu j) (fun _ => rfl)
      obtain ⟨Δ', h1, h2⟩ := ih s1 (dbup σ) hr nu'
      have h0 : vty_of (A ## Γ) (DVar 0) (Δ' 0) := by simpa using h1 0
      have AC : vsub A (Δ' 0) := gen_var h0
      have h2' : vty_of (Δ' 0 ## (fun i => Δ' (i + 1))) s1 B := by
        rw [scons_eta]; exact h2
      have d : vty_of (fun i => Δ' (i + 1)) (DAbs s1) (VArr A B) :=
        vty_of.vSub (vty_of.vAbs h2') (vsub.vs_arr AC (vsub.vs_refl _))
      refine ⟨fun i => Δ' (i + 1), fun i => ?_, d⟩
      have : vty_of (A ## Γ) (dbren (σ i) Nat.succ) (Δ' (i + 1)) := by simpa using h1 (i + 1)
      exact strengthen (ρ := Nat.succ) this
  | vApp _ _ ih1 ih2 =>
    rename_i Γ p A B q _ _
    intro s σ hr nu
    cases s with
    | DVar j =>
      have : σ j = DApp p q := hr.symm
      exact expand_var (this ▸ vty_of.vApp ‹_› ‹_›) nu
    | DAbs _ => simp at hr
    | DApp s1 s2 =>
      simp only [dbsub_App, dB.DApp.injEq] at hr
      obtain ⟨Δ1, a1, a2⟩ := ih1 s1 σ hr.1 nu
      obtain ⟨Δ2, b1, b2⟩ := ih2 s2 σ hr.2 nu
      refine ⟨cmeet Δ1 Δ2, fun i => vty_of.vInter (a1 i) (b1 i), ?_⟩
      exact vty_of.vApp (ctx_mono a2 (cle_meet1 _ _)) (ctx_mono b2 (cle_meet2 _ _))
  | @vNu Γ t =>
    intro s σ hr nu
    cases s with
    | DVar j =>
      have e : σ j = DAbs t := hr.symm
      exact expand_var (A := VNu) (by rw [e]; exact vty_of.vNu) nu
    | DApp _ _ => simp at hr
    | DAbs s1 => exact ⟨fun _ => VNu, nu, vty_of.vNu⟩
  | vInter _ _ ih1 ih2 =>
    intro s σ hr nu
    obtain ⟨Δ1, a1, a2⟩ := ih1 s σ hr nu
    obtain ⟨Δ2, b1, b2⟩ := ih2 s σ hr nu
    refine ⟨cmeet Δ1 Δ2, fun i => vty_of.vInter (a1 i) (b1 i), ?_⟩
    exact vty_of.vInter (ctx_mono a2 (cle_meet1 _ _)) (ctx_mono b2 (cle_meet2 _ _))
  | vSub _ hs ih =>
    intro s σ hr nu
    obtain ⟨Δ, a1, a2⟩ := ih s σ hr nu
    exact ⟨Δ, a1, vty_of.vSub a2 hs⟩

theorem expand_beta {Γ : Nat → vty} {s u : dB} {A : vty} (h : vty_of Γ (subst s u 0) A)
    (hu : vty_of Γ u VNu) : vty_of Γ (DApp (DAbs s) u) A := by
  rw [subst_sub] at h
  have nu : ∀ i, vty_of Γ (ins 0 u i) VNu := by
    intro i
    cases i with
    | zero => simpa [ins] using hu
    | succ j => simpa [ins] using vty_of.vSub (vty_of.vVar (i := j) rfl) (vsub.vs_nu (Γ j))
  obtain ⟨Δ, h1, h2⟩ := expand_aux h s (ins 0 u) rfl nu
  have h3 : ∀ i, vsub (Γ i) (Δ (i + 1)) := by
    intro i
    have : vty_of Γ (ins 0 u (i + 1)) (Δ (i + 1)) := h1 (i + 1)
    have : vty_of Γ (DVar i) (Δ (i + 1)) := by simpa [ins] using this
    exact gen_var this
  have h4 : vty_of (Δ 0 ## Γ) s A := by
    apply ctx_mono h2
    intro i
    cases i with
    | zero => exact vsub.vs_refl _
    | succ j => exact h3 j
  have h5 : vty_of Γ u (Δ 0) := by simpa [ins] using h1 0
  exact vty_of.vApp (vty_of.vAbs h4) h5

/-- Fireballs are typable; inert terms have every type. -/
theorem fb_typable (i : dB) :
    (dinert i → ∀ A, ∃ Γ : Nat → vty, vty_of Γ i A) ∧ (dfb i → ∃ Γ : Nat → vty, vty_of Γ i VNu) := by
  induction i with
  | DVar i =>
    have : ∀ A, ∃ Γ : Nat → vty, vty_of Γ (DVar i) A := fun A => ⟨fun _ => A, vty_of.vVar rfl⟩
    exact ⟨fun _ => this, fun _ => this VNu⟩
  | DAbs s _ =>
    exact ⟨fun h => (dinert_not_DAbs _ h).elim, fun _ => ⟨fun _ => VNu, vty_of.vNu⟩⟩
  | DApp s t ihs iht =>
    have inert : dinert s → dfb t → ∀ A, ∃ Γ : Nat → vty, vty_of Γ (DApp s t) A := by
      intro hs ht A
      obtain ⟨Γ2, g2⟩ := iht.2 ht
      obtain ⟨Γ1, g1⟩ := ihs.1 hs (VArr VNu A)
      exact ⟨cmeet Γ1 Γ2, vty_of.vApp (ctx_mono g1 (cle_meet1 _ _)) (ctx_mono g2 (cle_meet2 _ _))⟩
    exact ⟨fun h => inert (dinert_DApp_iff.1 h).1 (dinert_DApp_iff.1 h).2,
           fun h => inert (dfb_DApp_iff.1 h).1 (dfb_DApp_iff.1 h).2 VNu⟩

theorem refine_fb {Γ : Nat → vty} {u : dB} (h : dfb u) :
    ∃ Γ' : Nat → vty, cle Γ' Γ ∧ vty_of Γ' u VNu := by
  obtain ⟨Δ, hΔ⟩ := (fb_typable u).2 h
  exact ⟨cmeet Γ Δ, cle_meet1 _ _, ctx_mono hΔ (cle_meet2 _ _)⟩

theorem expand_app {Γ : Nat → vty} {r s s' t t' : dB} {A : vty} (h : vty_of Γ r A)
    (IH1 : ∀ (Γ : Nat → vty) (C : vty), vty_of Γ s' C → ∃ Γ', cle Γ' Γ ∧ vty_of Γ' s C)
    (IH2 : ∀ (Γ : Nat → vty) (C : vty), vty_of Γ t' C → ∃ Γ', cle Γ' Γ ∧ vty_of Γ' t C) :
    r = DApp s' t' → ∃ Γ' : Nat → vty, cle Γ' Γ ∧ vty_of Γ' (DApp s t) A := by
  induction h with
  | vVar _ => intro e; cases e
  | vAbs _ => intro e; cases e
  | vApp hp hq _ _ =>
    intro e
    cases e
    obtain ⟨Γ1, c1, d1⟩ := IH1 _ _ hp
    obtain ⟨Γ2, c2, d2⟩ := IH2 _ _ hq
    exact ⟨cmeet Γ1 Γ2, cle_trans (cle_meet1 _ _) c1,
      vty_of.vApp (ctx_mono d1 (cle_meet1 _ _)) (ctx_mono d2 (cle_meet2 _ _))⟩
  | vNu => intro e; cases e
  | vInter _ _ ih1 ih2 =>
    intro e
    obtain ⟨Γ1, c1, d1⟩ := ih1 e
    obtain ⟨Γ2, c2, d2⟩ := ih2 e
    exact ⟨cmeet Γ1 Γ2, cle_trans (cle_meet1 _ _) c1,
      vty_of.vInter (ctx_mono d1 (cle_meet1 _ _)) (ctx_mono d2 (cle_meet2 _ _))⟩
  | vSub _ hs ih =>
    intro e
    obtain ⟨Γ', c, d⟩ := ih e
    exact ⟨Γ', c, vty_of.vSub d hs⟩

theorem subject_expansion {t t' : dB} (h : vred t t') :
    ∀ {Γ : Nat → vty} {A : vty}, vty_of Γ t' A → ∃ Γ', cle Γ' Γ ∧ vty_of Γ' t A := by
  induction h with
  | vbeta s hf =>
    intro Γ A h
    obtain ⟨Γ', c, nu⟩ := refine_fb (Γ := Γ) hf
    exact ⟨Γ', c, expand_beta (ctx_mono h c) nu⟩
  | vappL t _ ih =>
    intro Γ A h
    exact expand_app h (fun Γ C h => ih h) (fun Γ C h => ⟨Γ, cle_refl _, h⟩) rfl
  | vappR hf _ ih =>
    intro Γ A h
    exact expand_app h (fun Γ C h => ⟨Γ, cle_refl _, h⟩) (fun Γ C h => ih h) rfl

/-! ### Completeness and the classical theorem -/

theorem classical_complete {t : dB} (h : lam_VN t) : ∃ (Γ : Nat → vty) (A : vty), vty_of Γ t A := by
  obtain ⟨u, r, nf⟩ := h
  have : ∃ (Γ : Nat → vty) (A : vty), vty_of Γ u A :=
    let ⟨Γ, h⟩ := (fb_typable u).2 (normal_dfb nf); ⟨Γ, VNu, h⟩
  induction r with
  | refl => exact this
  | step h _ ih =>
    obtain ⟨Γ, A, h1⟩ := ih nf this
    obtain ⟨Γ', _, h2⟩ := subject_expansion h h1
    exact ⟨Γ', A, h2⟩

theorem classical_VN {t : dB} : lam_VN t ↔ ∃ (Γ : Nat → vty) (A : vty), vty_of Γ t A :=
  ⟨classical_complete, fun ⟨_, _, h⟩ => classical_sound h⟩

end LambdaEnvCBV
