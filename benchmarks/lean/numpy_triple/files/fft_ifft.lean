-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
set_option linter.missingDocs false

/-- Complex number type for IFFT operations -/
structure Complex where
  re : Float
  im : Float
  deriving Repr

/-- Complex addition -/
instance : Add Complex where
  add z w := { re := z.re + w.re, im := z.im + w.im }

/-- Complex multiplication -/
instance : Mul Complex where
  mul z w := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }

/-- Complex scalar multiplication -/
instance : HMul Float Complex Complex where
  hMul s z := { re := s * z.re, im := s * z.im }

/-- Zero complex number -/
instance : Zero Complex where
  zero := { re := 0, im := 0 }

/-- Complex exponential function e^(iθ) -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }
/-- Sum of complex numbers over finite indices -/
def complexSum {n : Nat} (f : Fin n → Complex) : Complex :=
  match n with
  | 0 => 0
  | n + 1 =>
    let rec go : Fin (n + 1) → Complex
      | ⟨0, _⟩ => f ⟨0, by omega⟩
      | ⟨i + 1, h⟩ => f ⟨i + 1, h⟩ + go ⟨i, by omega⟩
    go ⟨n, by omega⟩
/-- Complex number vector type -/
abbrev ComplexVector (n : Nat) := Vector Complex n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ifft {n : Nat} (a : ComplexVector n) : Id (ComplexVector n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ifft_spec {n : Nat} (a : ComplexVector n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    ifft a
    ⦃⇓result => ⌜∀ k : Fin n,
        result.get k = (1.0 / n.toFloat) * complexSum (fun j =>
            a.get j * cexp (2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat))⌝⦄ := by
  sorry
-- </vc-theorems>