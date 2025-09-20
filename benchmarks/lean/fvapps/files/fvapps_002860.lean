-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_array (x : String) : String := sorry

theorem sort_array_sorted_int (n : Int) : 
  String.all (sort_array (toString n)) (fun c => c.isDigit) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_array_length_preserved_int (n : Int) : 
  (sort_array (toString n)).length = (toString n).length := sorry

theorem sort_array_sorted_str (s : String) : 
  ∀ i : Fin (s.length-1), (sort_array s).get ⟨i⟩ ≤ (sort_array s).get ⟨i+1⟩ := sorry

theorem sort_array_length_preserved_str (s : String) :
  (sort_array s).length = s.length := sorry

theorem sort_array_same_chars (s : String) :
  s.toList.length = (sort_array s).toList.length ∧
  ∀ c, c ∈ s.toList ↔ c ∈ (sort_array s).toList := sorry

theorem sort_array_empty :
  sort_array "" = "" := sorry
-- </vc-theorems>