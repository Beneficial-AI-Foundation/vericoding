-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Complex number type for FFT results -/
structure Complex where
  /-- Real part -/
  re : Float
  /-- Imaginary part -/
  im : Float

/-- Complex exponential function -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }
/-- Complex multiplication -/
instance : Mul Complex where
  mul z w := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }

/-- Zero complex number -/
instance : Zero Complex where
  zero := { re := 0, im := 0 }

/-- Complex addition -/
instance : Add Complex where
  add z w := { re := z.re + w.re, im := z.im + w.im }

/-- Convert Float to Complex -/
def Float.toComplex (x : Float) : Complex := { re := x, im := 0 }
/-- Sum of complex numbers over finite indices -/
def complexSum {n : Nat} (f : Fin n → Complex) : Complex :=
  match n with
  | 0 => 0
  | n + 1 =>
    let rec go : Fin (n + 1) → Complex
      | ⟨0, _⟩ => f ⟨0, by omega⟩
      | ⟨i + 1, h⟩ => f ⟨i + 1, h⟩ + go ⟨i, by omega⟩
    go ⟨n, by omega⟩
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rfft {n : Nat} (a : Vector Float n) : Id (Vector Complex ((n / 2) + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rfft_spec {n : Nat} (a : Vector Float n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    rfft a
    ⦃⇓result => ⌜∀ k : Fin ((n / 2) + 1), 
      result.get k = complexSum (fun j : Fin n =>
        (a.get j).toComplex * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat)) ∧
      -- DC component is real
      (if h0 : 0 < (n / 2) + 1 then (result.get ⟨0, h0⟩).im = 0 else True) ∧
      -- For even n, Nyquist frequency is real
      (n % 2 = 0 → (if hn : n / 2 < (n / 2) + 1 then (result.get ⟨n / 2, hn⟩).im = 0 else True))⌝⦄ := by
  sorry
-- </vc-theorems>