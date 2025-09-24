-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_rfftfreq (n : Nat) (d : Float) (h : n > 0) : Id (Vector Float (n / 2 + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_rfftfreq_spec (n : Nat) (d : Float) (h : n > 0) (hd : d > 0) :
    ⦃⌜n > 0 ∧ d > 0⌝⦄
    numpy_rfftfreq n d h
    ⦃⇓result => ⌜
      -- First element is always 0
      result.get ⟨0, by simp⟩ = 0 ∧
      -- Each element follows the frequency formula
      ∀ i : Fin (n / 2 + 1), result.get i = Float.ofNat i.val / (d * Float.ofNat n) ∧
      -- Last element is the Nyquist frequency
      result.get ⟨n / 2, by simp⟩ = Float.ofNat (n / 2) / (d * Float.ofNat n) ∧
      -- Monotonicity: frequencies are non-decreasing
      ∀ i j : Fin (n / 2 + 1), i.val ≤ j.val → result.get i ≤ result.get j
    ⌝⦄ := by
  sorry
-- </vc-theorems>