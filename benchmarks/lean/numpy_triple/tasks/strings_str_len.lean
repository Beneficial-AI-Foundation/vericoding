-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def str_len {n : Nat} (a : Vector String n) : Id (Vector Nat n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem str_len_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    str_len a
    ⦃⇓result => ⌜∀ i : Fin n,
      -- Basic correctness: result contains the length of each string
      result.get i = (a.get i).length ∧
      -- Non-negativity: lengths are always non-negative (natural numbers)
      result.get i ≥ 0 ∧
      -- Empty string property: empty strings have length 0
      (a.get i = "" ↔ result.get i = 0) ∧
      -- Single character property: single characters have length 1
      (a.get i ≠ "" ∧ (a.get i).drop 1 = "" → result.get i = 1) ∧
      -- Monotonicity property: longer strings have lengths ≥ shorter prefixes
      (∀ k : Nat, k ≤ (a.get i).length → 
        ((a.get i).take k).length ≤ result.get i) ∧
      -- Deterministic property: same string always gives same length
      (∀ j : Fin n, a.get i = a.get j → result.get i = result.get j) ∧
      -- Concatenation property: length is additive for concatenation
      (∀ s1 s2 : String, a.get i = s1 ++ s2 → 
        result.get i = s1.length + s2.length)⌝⦄ := by
  sorry
-- </vc-theorems>