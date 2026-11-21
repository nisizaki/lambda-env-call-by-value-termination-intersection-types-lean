# Call-by-Value Termination of λenv and its Characterization by Intersection Types (Lean 4)

Lean 4 formalization accompanying the paper

> Shin-ya Nishizaki and Shogo Murasaki.
> *Call-by-Value Termination of λenv and its Characterization by Intersection Types, Formalized in Isabelle/HOL.*

The paper's primary formalization is in Isabelle/HOL
(<https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types>). This repository contains a port of that
development to Lean 4: one Lean file per Isabelle theory, with the same definitions and
theorem names.

## Main results

```lean
theorem main_characterization    : Typ M ↔ CFN M
theorem main_characterization_SN : Typ M ↔ CFSN M
theorem Typ_imp_SN               : Typ M → SN_at cbv M
theorem NF_unique : Star cbv M N1 → NF N1 → Star cbv M N2 → NF N2 → N1 = N2
theorem main_characterization_any_order : Typ M ↔ CFSNn M
theorem conservativity : pure M →
  (Typ M ↔ lam_VN (rb M dB.DVar)) ∧ (lam_VN (rb M dB.DVar) ↔ CFSN M)
theorem classical_VN : lam_VN t ↔ ∃ Γ A, vty_of Γ t A
theorem classical_agreement : pure M → (Typ M ↔ ∃ Γ A, vty_of Γ (rb M dB.DVar) A)
```

All 16 Isabelle theories are ported (one Lean file each, same names). There is no
`sorry` or `axiom`; `#print axioms` for the main theorems reports only `propext`,
`Classical.choice` and `Quot.sound`. `autoImplicit` is disabled.

## Adaptations

- Sets of terms are predicates (`t ∈ S` becomes `S t`); `rtranclp` is `Star`.
- `Id`, `Extn`, `Comp` are the constructors `iden`, `extn`, `comp`; the types `ty`, `sub`,
  `hasty` are `Ty`, `Sub` (`≼`), `Hasty` (`⊢`).
- In `Sub`, the rule `s_env` is a theorem; the constructor `s_env_core` splits its
  existential premise (equivalent because `map_of` is functional).
- `snf` (σ-normal form) uses `Classical.choose` instead of Isabelle's `SOME`.
- The top-level `fb_typable` of `Completeness` is named `fb_typable_top`, since
  `VTypes` also has a `fb_typable`.
- Theorems with two Isabelle conclusions are stated as one conjunction.

## Building

Requires Lean 4 v4.33.1 (installed automatically by `elan` from `lean-toolchain`).
There are no dependencies beyond the Lean core library (no Mathlib).

```bash
lake build
```

To list the axioms used by a theorem, e.g.

```lean
import LambdaEnvCBV
#print axioms LambdaEnvCBV.main_characterization_SN
```

## File layout

```
LambdaEnvCBV.lean         root module (imports all files)
LambdaEnvCBV/*.lean       the 16 files, one per Isabelle theory
lakefile.toml, lean-toolchain, lake-manifest.json
```

## Related repositories

- Isabelle/HOL original (primary formalization of the paper):
  <https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types>
- Call-by-name (weak-head) counterpart:
  <https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types>
  (Isabelle/HOL) and
  <https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types-lean>
  (Lean 4)
- The same questions for λpenv:
  <https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types-lean>

## Authors

Shin-ya Nishizaki and Shogo Murasaki

## How to cite

Please cite the paper:

> Shin-ya Nishizaki and Shogo Murasaki.
> Call-by-Value Termination of λenv and its Characterization by Intersection Types,
> Formalized in Isabelle/HOL.

## License

MIT License (see [LICENSE](LICENSE)).
