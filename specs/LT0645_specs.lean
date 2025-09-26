-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strip {n : Nat} (a : Vector String n) (chars : Option String) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strip_spec {n : Nat} (a : Vector String n) (chars : Option String) :
    ⦃⌜True⌝⦄
    strip a chars
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Fundamental correctness: result matches expected behavior
      (chars.isNone → result = original.trim) ∧
      -- Length preservation or reduction: result is no longer than original
      (result.length ≤ original.length) ∧
      -- Substring property: result is a substring of original
      (∃ start : Nat, ∃ len : Nat, 
        start + len ≤ original.length ∧ 
        result = original.extract ⟨start⟩ ⟨start + len⟩) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character removal correctness: when chars is provided
      (chars.isSome →
        ∃ start : Nat, ∃ len : Nat,
        start + len ≤ original.length ∧ 
        result = original.extract ⟨start⟩ ⟨start + len⟩ ∧
        -- All stripped leading characters are in the chars set
        (∀ j : Nat, j < start → 
          ∃ c : Char, original.get? ⟨j⟩ = some c ∧ c ∈ chars.get!.toList) ∧
        -- All stripped trailing characters are in the chars set
        (∀ j : Nat, start + len < j → j < original.length →
          ∃ c : Char, original.get? ⟨j⟩ = some c ∧ c ∈ chars.get!.toList) ∧
        -- The first non-stripped character (if any) is not in chars
        (start < original.length → start + len > start →
          ∃ c : Char, original.get? ⟨start⟩ = some c ∧ c ∉ chars.get!.toList) ∧
        -- The last non-stripped character (if any) is not in chars
        (start + len > 0 → start + len ≤ original.length →
          ∃ c : Char, original.get? ⟨start + len - 1⟩ = some c ∧ c ∉ chars.get!.toList)) ∧
      -- Maximal stripping: result cannot have leading or trailing chars from the set removed
      (chars.isSome → 
        (result = "" ∨ 
         (∀ c : Char, c ∈ chars.get!.toList → 
           result.get? ⟨0⟩ ≠ some c ∧ result.back ≠ c))) ∧
      -- Composition property: strip is equivalent to rstrip(lstrip(...))
      (chars.isSome →
        ∃ intermediate : String,
        -- First apply lstrip
        (∃ k : Nat, k ≤ original.length ∧ 
         intermediate = original.drop k ∧
         (∀ j : Nat, j < k → 
           ∃ c : Char, original.get? ⟨j⟩ = some c ∧ c ∈ chars.get!.toList) ∧
         (k < original.length → 
           ∃ c : Char, original.get? ⟨k⟩ = some c ∧ c ∉ chars.get!.toList)) ∧
        -- Then apply rstrip to get final result
        (∃ suffix : String, 
          intermediate = result ++ suffix ∧
          (∀ c : Char, c ∈ suffix.toList → c ∈ chars.get!.toList) ∧
          (result = "" ∨ 
           ∀ c : Char, c ∈ chars.get!.toList → result.back ≠ c))) ∧
      -- Middle preservation: characters that remain are in the same order
      (∀ j k : Nat, j < k → k < result.length → 
        ∃ origJ origK : Nat, j < origJ → origJ < origK → origK < original.length →
          result.get? ⟨j⟩ = original.get? ⟨origJ⟩ ∧ 
          result.get? ⟨k⟩ = original.get? ⟨origK⟩)⌝⦄ := by
  sorry
-- </vc-theorems>