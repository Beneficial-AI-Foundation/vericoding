-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveTennisTournament (n : Nat) : List String := sorry

theorem even_n_returns_no {n : Nat} (h : n > 0) (h2 : n % 2 = 0) :
  solveTennisTournament n = ["NO"] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_n_first_element {n : Nat} (h : n > 0) (h2 : n % 2 = 1) :
  (solveTennisTournament n).head? = some "YES" := sorry

theorem odd_n_length {n : Nat} (h : n > 0) (h2 : n % 2 = 1) :
  (solveTennisTournament n).length = n + 1 := sorry

theorem odd_n_inner_row_length {n : Nat} (h : n > 0) (h2 : n % 2 = 1) :
  ∀ row ∈ (solveTennisTournament n).tail, String.length row = n := sorry

theorem odd_n_valid_chars {n : Nat} (h : n > 0) (h2 : n % 2 = 1) :
  ∀ row ∈ (solveTennisTournament n).tail, 
  ∀ c ∈ String.toList row, c = '0' ∨ c = '1' := sorry

theorem odd_n_row_ones_count {n : Nat} (h : n > 0) (h2 : n % 2 = 1) :
  ∀ row ∈ (solveTennisTournament n).tail,
  let ones := (String.toList row).filter (· = '1')
  ones.length = (n-1)/2 := sorry

theorem odd_n_col_ones_count {n : Nat} (h : n > 0) (h2 : n % 2 = 1) (j : Nat) (hj : j < n) :
  let rows := (solveTennisTournament n).tail
  let col := rows.map (λ row => String.get! row ⟨j⟩)
  (col.filter (· = '1')).length = (n-1)/2 := sorry

theorem odd_n_no_self_play {n : Nat} (h : n > 0) (h2 : n % 2 = 1) (i : Nat) (hi : i < n) :
  let rows := (solveTennisTournament n).tail
  let row := rows.get! i
  String.get! row ⟨i⟩ = '0' := sorry
-- </vc-theorems>