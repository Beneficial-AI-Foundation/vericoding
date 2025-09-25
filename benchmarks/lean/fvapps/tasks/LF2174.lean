-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_game (n : Nat) (r : Nat) (initial : List Int) (changes : List (Nat × Int)) : List Float :=
  sorry

def list_sum (l : List Int) : Int :=
  sorry

def list_average (l : List Int) : Float :=
  sorry

def list_update (l : List Int) (idx : Nat) (val : Int) : List Int :=
  sorry

def float_close (a b : Float) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_game_result_length {n r : Nat} {initial : List Int} {changes : List (Nat × Int)} :
  initial.length = 2^n →
  (∀ change, change ∈ changes → change.1 < 2^n) →
  (solve_game n r initial changes).length = r + 1 :=
sorry

theorem solve_game_averages {n r : Nat} {initial : List Int} {changes : List (Nat × Int)}
  (h_init : initial.length = 2^n)
  (h_changes : ∀ change, change ∈ changes → change.1 < 2^n)
  (i : Fin r)
  (h_changes_length : changes.length > i.val)
  (h_result_length : (solve_game n r initial changes).length > i.val) :
  let updated := list_update initial ((changes.get ⟨i.val, h_changes_length⟩).1) ((changes.get ⟨i.val, h_changes_length⟩).2)
  float_close ((solve_game n r initial changes).get ⟨i.val, h_result_length⟩) (list_average updated) :=
sorry

theorem solve_game_final_average {n r : Nat} {initial : List Int} {changes : List (Nat × Int)}
  (h_init : initial.length = 2^n)
  (h_changes : ∀ change, change ∈ changes → change.1 < 2^n)
  (h_r : r > 0)
  (h_changes_length : changes.length ≥ r)
  (h_idx : r - 1 < changes.length)
  (h_result_length : r < (solve_game n r initial changes).length) :
  let final_update := list_update initial ((changes.get ⟨r-1, h_idx⟩).1) ((changes.get ⟨r-1, h_idx⟩).2)
  float_close ((solve_game n r initial changes).get ⟨r, h_result_length⟩) (list_average final_update) :=
sorry

theorem solve_game_no_changes {n : Nat} {initial : List Int}
  (h_init : initial.length = 2^n)
  (h_all_ones : ∀ x, x ∈ initial → x = 1)
  (h_length : 0 < (solve_game n 0 initial []).length) :
  (solve_game n 0 initial []).length = 1 ∧
  float_close ((solve_game n 0 initial []).get ⟨0, h_length⟩) 1.0 :=
sorry
-- </vc-theorems>