import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → List Int)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Int) :=
  0 < result.length ∧
  result.length = n ∧
  let i := result.length-1;
  (i = 0 → result[0]! = 1) ∧ -- base case
  (i = 1 → result[1]! = 3) ∧
  (2 ≤ i ∧ i % 2 = 0 → result[i]! = 1 + i / 2) ∧
  (2 ≤ i ∧ i % 2 = 1 → result[i]! = result[i-2]! + result[i-1]! + (1 + (i+1) / 2)) ∧
  if i = 0 then true else result.take i = impl (i-1)
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

def implementation (n: Nat) : List Int := 
  let rec aux (k: Nat) : List Int :=
    if k = 0 then []
    else
      let prev := aux (k-1)
      let new_val : Int := 
        if k-1 = 0 then 1
        else if k-1 = 1 then 3  
        else if (k-1) % 2 = 0 then 1 + (k-1 : Int) / 2
        else prev[k-1-2]?.getD 0 + prev[k-1-1]?.getD 0 + (1 + ((k-1 : Int)+1) / 2)
      prev ++ [new_val]
  aux n

-- LLM HELPER
lemma aux_length (k: Nat) : (implementation.aux k).length = k := by
  unfold implementation.aux
  if hk : k = 0 then
    simp [hk]
  else
    simp [hk]
    rw [List.length_append, aux_length (k-1)]
    simp

-- LLM HELPER
lemma aux_take (k: Nat) (hk: k > 0) : 
  (implementation.aux k).take (k-1) = implementation.aux (k-1) := by
  unfold implementation.aux
  simp [Nat.pos_iff_ne_zero.mp hk]
  rw [List.take_append_of_le_length]
  simp [aux_length (k-1)]
  omega

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  if h : n = 0 then
    simp [h]
    use []
    constructor
    · rfl
    · simp
  else
    have hn_pos : n > 0 := Nat.pos_of_ne_zero h
    use implementation n
    constructor
    · rfl
    · constructor
      · simp [implementation]
        rw [aux_length n]
        exact hn_pos
      · constructor
        · simp [implementation]
          rw [aux_length n]
        · simp [implementation]
          rw [aux_length n]
          constructor
          · intro h0
            have : n = 1 := by omega
            rw [this]
            unfold implementation.aux
            simp
          · constructor
            · intro h1
              have : n = 2 := by omega
              rw [this]
              unfold implementation.aux
              simp
            · constructor
              · intro h_even
                have : n ≥ 3 := by omega
                unfold implementation.aux
                simp [Nat.pos_iff_ne_zero.mp hn_pos]
                rw [List.get!_append_right]
                simp [aux_length (n-1)]
                rw [List.get!_cons_zero]
                simp
                by_cases h01 : n - 1 = 0
                · omega
                · by_cases h11 : n - 1 = 1
                  · omega
                  · simp [h01, h11, h_even.2]
              · constructor
                · intro h_odd
                  have : n ≥ 3 := by omega
                  unfold implementation.aux
                  simp [Nat.pos_iff_ne_zero.mp hn_pos]
                  rw [List.get!_append_right]
                  simp [aux_length (n-1)]
                  rw [List.get!_cons_zero]
                  simp
                  by_cases h01 : n - 1 = 0
                  · omega
                  · by_cases h11 : n - 1 = 1
                    · omega
                    · simp [h01, h11, h_odd.2]
                · by_cases h_n : n = 1
                  · simp [h_n]
                  · simp [h_n]
                    exact aux_take n hn_pos