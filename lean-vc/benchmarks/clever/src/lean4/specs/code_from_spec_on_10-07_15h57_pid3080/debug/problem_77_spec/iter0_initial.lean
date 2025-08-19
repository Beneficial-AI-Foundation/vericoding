import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  result ↔ exists n: Int, a = n^3
-- program termination
∃ result, implementation a = result ∧
spec result

-- LLM HELPER
def cubeRoot (a: Int) : Int :=
  if a = 0 then 0
  else if a > 0 then
    Nat.cast (Nat.sqrt (Int.natAbs a))
  else
    -(Nat.cast (Nat.sqrt (Int.natAbs a)))

-- LLM HELPER
def isPerfectCube (a: Int) : Bool :=
  let r := cubeRoot a
  (r^3 = a) || ((r+1)^3 = a) || ((r-1)^3 = a)

def implementation (a: Int) : Bool := isPerfectCube a

-- LLM HELPER
lemma cubeRoot_spec (a: Int) : ∃ n: Int, (n^3 ≤ a ∧ a < (n+1)^3) ∨ (n^3 = a) := by
  sorry

-- LLM HELPER
lemma isPerfectCube_correct (a: Int) : isPerfectCube a = true ↔ ∃ n: Int, a = n^3 := by
  constructor
  · intro h
    unfold isPerfectCube at h
    let r := cubeRoot a
    simp at h
    cases' h with h1 h2
    · use r
      exact h1
    · cases' h2 with h2 h3
      · use r + 1
        exact h2
      · use r - 1
        exact h3
  · intro ⟨n, hn⟩
    unfold isPerfectCube
    let r := cubeRoot a
    simp
    by_cases h : r^3 = a
    · left
      exact h
    · by_cases h2 : (r+1)^3 = a
      · right
        left
        exact h2
      · right
        right
        rw [← hn]
        ring_nf
        sorry

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  unfold problem_spec
  use implementation a
  constructor
  · rfl
  · intro result
    constructor
    · intro h
      rw [← h]
      unfold implementation
      have := isPerfectCube_correct a
      exact this.mp
    · intro h
      unfold implementation
      have := isPerfectCube_correct a
      cases' h with n hn
      rw [this.mpr ⟨n, hn⟩]
      simp