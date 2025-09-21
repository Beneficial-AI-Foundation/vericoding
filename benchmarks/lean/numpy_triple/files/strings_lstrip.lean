-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lstrip {n : Nat} (a : Vector String n) (chars : Option String) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lstrip_spec {n : Nat} (a : Vector String n) (chars : Option String) :
    ⦃⌜True⌝⦄
    lstrip a chars
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Fundamental correctness: result matches expected behavior
      (chars.isNone → result = original.trimLeft) ∧
      -- Length preservation or reduction: result is no longer than original
      (result.length ≤ original.length) ∧
      -- Suffix property: result is a suffix of original
      (∃ k : Nat, k ≤ original.length ∧ result = original.drop k) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character removal correctness: when chars is provided
      (chars.isSome →
        ∃ k : Nat, k ≤ original.length ∧ 
        result = original.drop k ∧
        -- All stripped characters are in the chars set
        (∀ j : Nat, j < k → 
          ∃ c : Char, original.get? ⟨j⟩ = some c ∧ c ∈ chars.get!.toList) ∧
        -- The first non-stripped character (if any) is not in chars
        (k < original.length → 
          ∃ c : Char, original.get? ⟨k⟩ = some c ∧ c ∉ chars.get!.toList)) ∧
      -- Minimal stripping: no more characters should be removed
      (chars.isSome → 
        ∀ k' : Nat, k' < result.length → 
          ∃ c : Char, result.get? ⟨k'⟩ = some c ∧ c ∉ chars.get!.toList) ∧
      -- Idempotent-like property: applying lstrip to result with same chars removes nothing
      (chars.isSome → 
        ∀ c : Char, result.get? ⟨0⟩ = some c → c ∉ chars.get!.toList)⌝⦄ := by
  sorry
-- </vc-theorems>