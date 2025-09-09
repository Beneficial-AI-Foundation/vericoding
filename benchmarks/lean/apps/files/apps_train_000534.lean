-- <vc-helpers>
-- </vc-helpers>

def generate_pattern (k : Nat) : List String :=
  sorry

theorem pattern_length {k : Nat} (h : k > 0) :
  (generate_pattern k).length = 2 * k :=
  sorry

theorem paired_lines {k : Nat} (h : k > 0) :
  ∀ i, i < k → 
    List.get! (generate_pattern k) (2*i) = List.get! (generate_pattern k) (2*i + 1) :=
  sorry

theorem pattern_contents {k : Nat} (h : k > 0) :
  ∀ line ∈ generate_pattern k,
    ∀ c ∈ line.data, c = '*' :=
  sorry

theorem increasing_widths {k : Nat} (h : k > 0) :
  ∀ i, i < k - 1 →
    (List.get! (generate_pattern k) (2*i)).length < (List.get! (generate_pattern k) (2*i + 2)).length :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded