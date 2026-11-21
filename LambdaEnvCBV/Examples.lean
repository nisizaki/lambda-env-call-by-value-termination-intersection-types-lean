import LambdaEnvCBV.Main_Results

/-!
# Examples

Port of `Examples.thy`.  A criterion for divergence, and the standard examples: `Ω`, `K Ω`
(divergent in call-by-value), an abstraction with divergent body (a value), lazy environments,
and a clash.
-/

namespace LambdaEnvCBV

open Trm

/-! ## A criterion for divergence -/

theorem cd_fwd_sig_steps {M M' : Trm} {n : Nat} {E : Trm} (r : Star Sig M M') (c : cd M n E) :
    cd M' n E := by
  induction r with
  | refl => exact c
  | step s _ ih => exact ih (cd_fwd_sig s c)

/-- A term that returns to itself through a β_v-step has no normal form. -/
theorem loop_not_CFN {M M1 : Trm} (b : beta M M1) (s : Star Sig M1 M) : ¬ CFN M := by
  rintro ⟨N, r, n, _⟩
  obtain ⟨k, c⟩ := steps_cd r n
  obtain ⟨j, hk, c1⟩ := cd_fwd_beta b c
  have c2 : cd M j N := cd_fwd_sig_steps s c1
  have := (cd_det c (n' := j) c2).1
  omega

/-! ## Helper lemmas: σ-normality of concrete shapes -/

theorem sn_Var (x : Var) : sig_normal (var x) := fun _ h => by cases h

theorem sn_Lam {M : Trm} {x : Var} (h : sig_normal M) : sig_normal (lam x M) := by
  intro N hN; cases hN with
  | Lam _ h' => exact h _ h'

theorem sn_App {M N : Trm} (h1 : sig_normal M) (h2 : sig_normal N) : sig_normal (app M N) := by
  intro P hP; cases hP with
  | AppL _ h' => exact h1 _ h'
  | AppR _ h' => exact h2 _ h'

theorem sn_Clo {M E : Trm} (x : Var) (hM : sig_normal M) (hE : sig_normal E) (hne : E ≠ iden) :
    sig_normal (comp (lam x M) E) := by
  intro P hP; cases hP with
  | IdR => exact hne rfl
  | CompL _ h => cases h with | Lam _ h' => exact hM _ h'
  | CompR _ h => exact hE _ h

theorem sn_Extn {M N : Trm} {x : Var} (h1 : sig_normal M) (h2 : sig_normal N) :
    sig_normal (extn M x N) := by
  intro P hP; cases hP with
  | ExtnL _ _ h => exact h1 _ h
  | ExtnR _ _ h => exact h2 _ h

/-! ## Terms -/

def dw : Trm := lam 0 (app (var 0) (var 0))
def Omega : Trm := app dw dw
def K : Trm := lam 0 (lam 1 (var 1))

theorem sn_dw : sig_normal dw := sn_Lam (sn_App (sn_Var 0) (sn_Var 0))

theorem Omega_loop :
    beta Omega (comp (app (var 0) (var 0)) (extn dw 0 iden)) ∧
    Star Sig (comp (app (var 0) (var 0)) (extn dw 0 iden)) Omega := by
  refine ⟨beta.Beta2 0 (app (var 0) (var 0)) (.FLam 0 _), ?_⟩
  have s1 : Sig (comp (app (var 0) (var 0)) (extn dw 0 iden))
      (app (comp (var 0) (extn dw 0 iden)) (comp (var 0) (extn dw 0 iden))) := .DApp _ _ _
  have s2 : Sig (app (comp (var 0) (extn dw 0 iden)) (comp (var 0) (extn dw 0 iden)))
      (app dw (comp (var 0) (extn dw 0 iden))) := .AppL _ (.VarRef 0 dw iden)
  have s3 : Sig (app dw (comp (var 0) (extn dw 0 iden))) (app dw dw) :=
    .AppR _ (.VarRef 0 dw iden)
  exact .step s1 (.step s2 (.single s3))

theorem Omega_not_Typ : ¬ Typ Omega :=
  fun h => loop_not_CFN Omega_loop.1 Omega_loop.2 (main_characterization.1 h)

/-- The argument is evaluated first, so `K Ω` diverges in call-by-value
(in the call-by-name system it is typable). -/
theorem K_Omega_not_Typ : ¬ Typ (app K Omega) := by
  have b : beta (app K Omega) (app K (comp (app (var 0) (var 0)) (extn dw 0 iden))) :=
    .AppR (.FLam 0 _) Omega_loop.1
  have s : Star Sig (app K (comp (app (var 0) (var 0)) (extn dw 0 iden))) (app K Omega) :=
    sig_steps_lift (f := fun P => app K P) (fun _ _ h => .AppR K h) Omega_loop.2
  exact fun h => loop_not_CFN b s (main_characterization.1 h)

/-- An abstraction is a value even if its body diverges. -/
theorem K_lam_Omega_Typ : Typ (app K (lam 2 Omega)) := by
  have b : beta (app K (lam 2 Omega)) (comp (lam 1 (var 1)) (extn (lam 2 Omega) 0 iden)) :=
    .Beta2 0 (lam 1 (var 1)) (.FLam 2 _)
  have hn : NF (comp (lam 1 (var 1)) (extn (lam 2 Omega) 0 iden)) :=
    fb_NF (.FClo _ _ _)
      (sn_Clo 1 (sn_Var 1) (sn_Extn (sn_Lam (sn_App sn_dw sn_dw)) (fun _ h => by cases h))
        (by intro h; cases h))
  have c : CFN (app K (lam 2 Omega)) :=
    ⟨_, .single (beta_imp_cbv b), hn, .FClo _ _ _⟩
  exact main_characterization.2 c

/-- Environments are lazy: a divergent component that is never looked up is harmless. -/
theorem lazy_env_Typ : Typ (comp (var 1) (extn Omega 0 (extn (var 2) 1 iden))) := by
  have s1 : Sig (comp (var 1) (extn Omega 0 (extn (var 2) 1 iden)))
      (comp (var 1) (extn (var 2) 1 iden)) := .VarSkip _ _ (by decide)
  have s2 : Sig (comp (var 1) (extn (var 2) 1 iden)) (var 2) := .VarRef _ _ _
  have c : CFN (comp (var 1) (extn Omega 0 (extn (var 2) 1 iden))) :=
    ⟨var 2, .step (sig_imp_cbv s1) (.step (sig_imp_cbv s2) (.refl _)), NF_Var 2, fb_Var 2⟩
  exact main_characterization.2 c

/-- Applying an environment is a clash. -/
theorem clash_example : ¬ Typ (app iden iden) := by
  refine clash_not_Typ ?_ ?_
  · rintro b (h | h)
    · cases h with
      | AppL _ h => exact sig_Id_no _ h
      | AppR _ h => exact sig_Id_no _ h
    · cases h with
      | AppL _ b => exact Id_no_beta b
      | AppR _ b => exact Id_no_beta b
  · exact fun h => not_inert_Id (fb_App_iff.1 h).1

end LambdaEnvCBV
