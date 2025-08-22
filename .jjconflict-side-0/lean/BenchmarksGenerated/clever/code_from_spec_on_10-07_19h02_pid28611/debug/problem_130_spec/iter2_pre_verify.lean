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
def build_list (n: Nat) : List Int :=
  let rec aux (k: Nat) : List Int :=
    if k = 0 then []
    else
      let prev := aux (k-1)
      let new_val := 
        if k-1 = 0 then 1
        else if k-1 = 1 then 3
        else if (k-1) % 2 = 0 then 1 + (k-1) / 2
        else prev[k-1-2]! + prev[k-1-1]! + (1 + ((k-1)+1) / 2)
      prev ++ [new_val]
  aux n

def implementation (n: Nat) : List Int := build_list n

-- LLM HELPER
lemma build_list_length (n: Nat) : (build_list n).length = n := by
  unfold build_list
  let rec aux_length (k: Nat) : (build_list.aux k).length = k := by
    unfold build_list.aux
    if hk : k = 0 then
      simp [hk]
    else
      simp [hk]
      rw [List.length_append, aux_length (k-1)]
      simp
  exact aux_length n

-- LLM HELPER
lemma build_list_nonempty (n: Nat) (h: n > 0) : (build_list n).length > 0 := by
  rw [build_list_length]
  exact h

-- LLM HELPER
lemma build_list_get_last (n: Nat) (h: n > 0) : 
  (build_list n)[n-1]! = 
    if n-1 = 0 then 1
    else if n-1 = 1 then 3
    else if (n-1) % 2 = 0 then 1 + (n-1) / 2
    else (build_list n)[n-1-2]! + (build_list n)[n-1-1]! + (1 + ((n-1)+1) / 2) := by
  unfold build_list
  let rec aux_get_last (k: Nat) (hk: k > 0) : 
    (build_list.aux k)[k-1]! = 
      if k-1 = 0 then 1
      else if k-1 = 1 then 3
      else if (k-1) % 2 = 0 then 1 + (k-1) / 2
      else (build_list.aux k)[k-1-2]! + (build_list.aux k)[k-1-1]! + (1 + ((k-1)+1) / 2) := by
    unfold build_list.aux
    simp [Nat.pos_iff_ne_zero.mp hk]
    rw [List.get!_append_right]
    · simp
    · rw [build_list_length]
      omega
  exact aux_get_last n h

-- LLM HELPER  
lemma build_list_take (n: Nat) (h: n > 0) : 
  (build_list n).take (n-1) = build_list (n-1) := by
  unfold build_list
  let rec aux_take (k: Nat) (hk: k > 0) : 
    (build_list.aux k).take (k-1) = build_list.aux (k-1) := by
    unfold build_list.aux
    simp [Nat.pos_iff_ne_zero.mp hk]
    rw [List.take_append_of_le_length]
    · simp
    · rw [build_list_length]
      omega
  exact aux_take n h

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
            simp [build_list_get_last 1 (by omega)]
            simp
          · constructor
            · intro h1
              have : n = 2 := by omega
              rw [this]
              simp [build_list_get_last 2 (by omega)]
              simp
            · constructor
              · intro h_even
                have : n ≥ 3 := by omega
                rw [build_list_get_last n hn_pos]
                simp [h_even.2]
                by_cases h01 : n - 1 = 0
                · omega
                · by_cases h11 : n - 1 = 1
                  · omega
                  · simp [h01, h11]
              · constructor
                · intro h_odd
                  have : n ≥ 3 := by omega
                  rw [build_list_get_last n hn_pos]
                  simp [h_odd.2]
                  by_cases h01 : n - 1 = 0
                  · omega
                  · by_cases h11 : n - 1 = 1
                    · omega
                    · simp [h01, h11]
                      rw [Nat.mod_two_eq_one] at h_odd
                      simp [h_odd.2]
                · by_cases h_n : n = 1
                  · simp [h_n]
                  · simp [h_n]
                    rw [build_list_take n hn_pos]