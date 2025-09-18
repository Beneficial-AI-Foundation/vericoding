-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dup (strings : List String) : List String := sorry

theorem dup_same_length (strings : List String) (h : strings ≠ []) : 
  List.length (dup strings) = List.length strings := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dup_no_consecutive_duplicates (strings : List String) (h : strings ≠ []) :
  ∀ s ∈ dup strings, ∀ i, i + 1 < s.length → 
  s.data[i]? = some c₁ → s.data[i+1]? = some c₂ → c₁ ≠ c₂ :=
sorry

theorem dup_chars_from_input (strings : List String) (h : strings ≠ []) :
  ∀ (out_str : String), out_str ∈ dup strings → 
  ∀ (in_str : String), in_str ∈ strings → 
  ∀ c, c ∈ out_str.data → c ∈ in_str.data :=
sorry

theorem dup_preserves_order (strings : List String) (h : strings ≠ []) :
  ∀ (out_str : String), out_str ∈ dup strings →
  ∀ (in_str : String), in_str ∈ strings →
  ∀ i j, i < j → i < out_str.length → j < out_str.length →
  out_str.data[i]? = out_str.data[j]? → i + 1 < j :=
sorry

theorem dup_output_length (strings : List String) (h : strings ≠ []) (h2 : ∀ s ∈ strings, s.length > 0) :
  ∀ s ∈ dup strings, s.length ≤ List.foldl (fun acc x => max acc x.length) 0 strings :=
sorry
-- </vc-theorems>