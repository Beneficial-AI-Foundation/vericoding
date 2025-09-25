-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
set_option linter.missingDocs false

/-- Complex number type for IFFTN operations -/
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
def ifftn {m n : Nat} (a : Vector (ComplexVector n) m) : Id (Vector (ComplexVector n) m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ifftn_spec {m n : Nat} (a : Vector (ComplexVector n) m) (hm : m > 0) (hn : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    ifftn a
    ⦃⇓result => ⌜∀ i : Fin m, ∀ j : Fin n,
        (result.get i).get j = (1.0 / (m.toFloat * n.toFloat)) * 
        complexSum (fun k => complexSum (fun l =>
            (a.get k).get l * cexp (2 * (3.14159265358979323846 : Float) * 
                (i.val.toFloat * k.val.toFloat / m.toFloat + j.val.toFloat * l.val.toFloat / n.toFloat))))⌝⦄ := by
  sorry
-- </vc-theorems>