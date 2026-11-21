import LambdaEnvCBV.VTypes
import LambdaEnvCBV.Readback

/-!
# Agreement with a classical call-by-value intersection-type system

Port of `Classical.thy`.

For pure terms, λenv typability agrees with typability of the readback in the classical system
of `VTypes`.  Both characterize normalizability of the readback in Open CBV (`conservativity`
and `classical_VN`); the agreement is obtained through this common characterization, not by a
syntactic translation of derivations.
-/

namespace LambdaEnvCBV

open dB

theorem classical_agreement {M : Trm} (h : pure M) :
    Typ M ↔ ∃ (Γ : Nat → vty) (A : vty), vty_of Γ (rb M DVar) A :=
  (conservativity h).1.trans classical_VN

end LambdaEnvCBV
