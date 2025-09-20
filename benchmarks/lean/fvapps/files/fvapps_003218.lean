-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_column_title (n : Int) : String := sorry

theorem get_column_title_type_error_non_integer :
  ∀ x : Int, x > 0 → get_column_title x ≠ "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_column_title_index_error_zero_neg :
  ∀ n : Int, n ≤ 0 → get_column_title n = "" := sorry

theorem get_column_title_uppercase_only :
  ∀ n : Int, n > 0 → 
  ∀ i : Nat, i < (get_column_title n).length → 
  let c := (get_column_title n).data[i]? 
  ∀ v, c = some v → 'A' ≤ v ∧ v ≤ 'Z' := sorry

theorem get_column_title_length_constraints :
  ∀ n : Int, n > 0 → 
  let result := get_column_title n
  let n_str := toString n
  1 ≤ result.length ∧ 
  result.length ≤ n_str.length ∧
  result.length ≥ (n_str.length + 1) / 2 := sorry

theorem get_column_title_single_letter :
  ∀ n : Int, 1 ≤ n ∧ n ≤ 26 →
  let result := get_column_title n
  result.length = 1 ∧ 
  result.data[0]? = some (Char.ofNat (n.toNat + 64)) := sorry

theorem get_column_title_monotonic :
  ∀ n : Int, n > 0 →
  get_column_title n < get_column_title (n + 1) := sorry
-- </vc-theorems>