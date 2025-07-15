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

-- LLM HELPER
def compute_value (i: Nat) (prev_list: List Int) : Int :=
  if i = 0 then 1
  else if i = 1 then 3
  else if i % 2 = 0 then 1 + i / 2
  else prev_list[i-2]! + prev_list[i-1]! + (1 + (i+1) / 2)

-- LLM HELPER
def build_list (n: Nat) : List Int :=
  if n = 0 then []
  else
    let rec aux (k: Nat) (acc: List Int) : List Int :=
      if k = 0 then acc
      else
        let new_val := compute_value (acc.length) acc
        aux (k-1) (acc ++ [new_val])
    aux n []

def implementation (n: Nat) : List Int := build_list n

-- LLM HELPER
lemma build_list_length (n: Nat) : (build_list n).length = n := by
  unfold build_list
  if h : n = 0 then
    simp [h]
  else
    simp [h]
    let rec aux_length (k: Nat) (acc: List Int) : (build_list.aux k acc).length = k + acc.length := by
      unfold build_list.aux
      if hk : k = 0 then
        simp [hk]
      else
        simp [hk]
        rw [aux_length (k-1) (acc ++ [compute_value acc.length acc])]
        simp [List.length_append]
        omega
    have : build_list.aux n [] = build_list n := by simp [build_list]
    rw [← this]
    rw [aux_length n []]
    simp

-- LLM HELPER
lemma build_list_nonempty (n: Nat) (h: n > 0) : (build_list n).length > 0 := by
  rw [build_list_length]
  exact h

-- LLM HELPER
lemma build_list_get (n: Nat) (i: Nat) (hi: i < n) : 
  (build_list n)[i]! = compute_value i (build_list i) := by
  unfold build_list
  if hn : n = 0 then
    simp [hn] at hi
  else
    simp [hn]
    let rec aux_get (k: Nat) (acc: List Int) (j: Nat) (hj: j < k + acc.length) :
      j < acc.length ∨ (build_list.aux k acc)[j]! = compute_value (acc.length + (j - acc.length)) 
        (build_list (acc.length + (j - acc.length))) := by
      unfold build_list.aux
      if hk : k = 0 then
        simp [hk] at hj
        left
        exact hj
      else
        simp [hk]
        by_cases h : j < acc.length
        · right
          simp [List.get!_append_left h]
          sorry
        · right
          simp [List.get!_append_right h]
          sorry
    sorry

-- LLM HELPER
lemma build_list_take (n: Nat) (h: n > 0) : 
  (build_list n).take (n-1) = build_list (n-1) := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  if h : n = 0 then
    simp [h, build_list]
  else
    have hn_pos : n > 0 := Nat.pos_of_ne_zero h
    use build_list n
    constructor
    · rfl
    · constructor
      · exact build_list_nonempty n hn_pos
      · constructor
        · exact build_list_length n
        · simp
          have i_eq : n - 1 = (build_list n).length - 1 := by
            rw [build_list_length]
          rw [← i_eq]
          constructor
          · intro h0
            have : n = 1 := by omega
            rw [this]
            simp [build_list, compute_value]
            unfold build_list.aux
            simp [compute_value]
          · constructor
            · intro h1
              have : n = 2 := by omega
              rw [this]
              simp [build_list, compute_value]
              unfold build_list.aux
              simp [compute_value]
            · constructor
              · intro h_even
                have : n ≥ 3 := by omega
                rw [build_list_get n (n-1) (by omega)]
                simp [compute_value]
                rw [h_even.2]
                simp
              · constructor
                · intro h_odd
                  have : n ≥ 3 := by omega
                  rw [build_list_get n (n-1) (by omega)]
                  simp [compute_value]
                  rw [h_odd.2]
                  simp
                  sorry
                · by_cases h_n : n = 1
                  · simp [h_n]
                  · simp [h_n]
                    rw [build_list_take n hn_pos]