-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VCHelpers

-- LLM HELPER: equivalence between Finset equality and element-wise membership
theorem finset_eq_iff_forall_mem {l₀ l₁ : List Char} :
    l₀.toFinset = l₁.toFinset ↔ ∀ c : Char, c ∈ l₀ ↔ c ∈ l₁ := by
  classical
  constructor
  · intro hx c
    constructor
    · intro hc
      have hc0 : c ∈ l₀.toFinset := by
        simpa [List.mem_toFinset] using hc
      have hc1 : c ∈ l₁.toFinset := by
        simpa [hx] using hc0
      simpa [List.mem_toFinset] using hc1
    · intro hc
      have hc1 : c ∈ l₁.toFinset := by
        simpa [List.mem_toFinset] using hc
      have hc0 : c ∈ l₀.toFinset := by
        simpa [hx] using hc1
      simpa [List.mem_toFinset] using hc0
  · intro h
    apply Finset.ext
    intro c
    have hciff := h c
    simpa [List.mem_toFinset] using hciff

end VCHelpers
-- </vc-helpers>

-- <vc-definitions>
def implementation (s0 s1: String) : Bool :=
  decide (s0.toList.toFinset = s1.toList.toFinset)
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(s0 s1: String) :=
-- spec
let spec (res: Bool) :=
  res ↔ (∀ c : Char, c ∈ s0.toList ↔ c ∈ s1.toList)
-- program terminates
∃ result, impl s0 s1 = result ∧
-- return value satisfies spec
spec result
-- if result then spec else ¬spec

theorem correctness
(s0 s1: String)
: problem_spec implementation s0 s1  := by
  classical
dsimp [problem_spec]
refine ⟨implementation s0 s1, rfl, ?_⟩
dsimp [implementation]
have hset :
    (s0.toList.toFinset = s1.toList.toFinset) ↔
      (∀ c : Char, c ∈ s0.toList ↔ c ∈ s1.toList) := by
  simpa using
    (VCHelpers.finset_eq_iff_forall_mem
      (l₀ := s0.toList) (l₁ := s1.toList))
by_cases hx : s0.toList.toFinset = s1.toList.toFinset
· simpa [hx, hset]
· simpa [hx, hset]
-- </vc-theorems>

-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddeddabc' = true
-- #test implementation 'abcd' 'dddddddabc' = true
-- #test implementation 'dddddddabc' 'abcd' = true
-- #test implementation 'eabcd' 'dddddddabc' = false
-- #test implementation 'abcd' 'dddddddabce' = false
-- #test implementation 'eabcdzzzz' 'dddzzzzzzzddddabc' = false