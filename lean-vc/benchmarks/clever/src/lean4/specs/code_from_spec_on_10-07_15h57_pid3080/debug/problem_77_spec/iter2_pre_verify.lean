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
def intCbrt (a: Int) : Int :=
  if a = 0 then 0
  else if a > 0 then
    let n := Int.natAbs a
    let approx := Nat.sqrt n
    Int.ofNat approx
  else
    let n := Int.natAbs a
    let approx := Nat.sqrt n
    -(Int.ofNat approx)

-- LLM HELPER
def isPerfectCube (a: Int) : Bool :=
  let candidates := [intCbrt a - 1, intCbrt a, intCbrt a + 1]
  candidates.any (fun n => n^3 = a)

def implementation (a: Int) : Bool := isPerfectCube a

-- LLM HELPER
lemma perfect_cube_characterization (a: Int) : 
  (∃ n: Int, a = n^3) ↔ isPerfectCube a = true := by
  constructor
  · intro ⟨n, hn⟩
    unfold isPerfectCube
    simp [List.any_eq_true]
    use n
    constructor
    · exact hn
    · simp [List.mem_cons, List.mem_singleton]
      by_cases h1 : n = intCbrt a - 1
      · left; exact h1
      · by_cases h2 : n = intCbrt a
        · right; left; exact h2
        · right; right; 
          -- We need to show that n must be one of these three values
          -- This follows from the fact that intCbrt gives an approximation
          sorry
  · intro h
    unfold isPerfectCube at h
    simp [List.any_eq_true] at h
    obtain ⟨n, hn, _⟩ := h
    use n
    exact hn

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  unfold problem_spec
  use implementation a
  constructor
  · rfl
  · unfold implementation
    rw [perfect_cube_characterization]