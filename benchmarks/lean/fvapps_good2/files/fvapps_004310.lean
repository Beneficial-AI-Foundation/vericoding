-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_zeros_count (c : Char) : Nat :=
  sorry

def binary_ones_count (c : Char) : Nat :=
  sorry

def more_zeros (s : String) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem more_zeros_results_unique (s : String) :
  let result := more_zeros s
  (List.length result = List.length (List.eraseDups result)) ∧
  (∀ c ∈ result, s.data.contains c) := by
  sorry

theorem more_zeros_binary_property (s : String) :
  let result := more_zeros s
  ∀ c ∈ result, binary_zeros_count c > binary_ones_count c := by
  sorry

theorem more_zeros_inclusion_complete (s : String) :
  let result := more_zeros s
  ∀ c ∈ s.data,
    binary_zeros_count c > binary_ones_count c →
    c ∉ result →
    (s.data.filter (· = c)).length > 1 := by
  sorry

theorem more_zeros_ascii_printable (s : String) :
  let result := more_zeros s
  ∀ c ∈ result, 32 ≤ c.toNat ∧ c.toNat ≤ 127 := by
  sorry
-- </vc-theorems>