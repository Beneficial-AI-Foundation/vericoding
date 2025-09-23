-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- SFC64 state containing 256 bits split into four 64-bit words -/
structure SFC64State where
  a : UInt64
  b : UInt64  
  c : UInt64
  counter : UInt64
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sfc64 (seed : Option UInt64) : Id SFC64State :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sfc64_spec (seed : Option UInt64) :
    ⦃⌜True⌝⦄
    sfc64 seed
    ⦃⇓state => ⌜(seed.isNone → state.a = 0 ∧ state.b = 0 ∧ state.c = 0 ∧ state.counter = 0) ∧
                 (seed.isSome → ∃ s : UInt64, seed = some s ∧ 
                   (state.a ≠ 0 ∨ state.b ≠ 0 ∨ state.c ≠ 0 ∨ state.counter ≠ 0)) ∧
                 (∀ s1 s2 : UInt64, s1 ≠ s2 → 
                   ∃ state1 state2 : SFC64State, 
                     (sfc64 (some s1)).run = state1 ∧ (sfc64 (some s2)).run = state2 ∧
                     (state1.a ≠ state2.a ∨ state1.b ≠ state2.b ∨ state1.c ≠ state2.c ∨ state1.counter ≠ state2.counter))⌝⦄ := by
  sorry
-- </vc-theorems>