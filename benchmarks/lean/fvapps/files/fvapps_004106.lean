-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def heavy_metal_umlauts (s : String) : String := sorry

theorem length_preserved (s : String) :
  (heavy_metal_umlauts s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_vowels_unchanged (s : String) (i : Nat) (h : i < s.length) :
  let c := s.data[i]
  let h' : i < (heavy_metal_umlauts s).length := by rw [length_preserved s]; exact h
  c ∉ ['A', 'E', 'I', 'O', 'U', 'Y', 'a', 'e', 'i', 'o', 'u', 'y'] →
  (heavy_metal_umlauts s).data[i] = c := sorry

theorem idempotent (s : String) :
  heavy_metal_umlauts (heavy_metal_umlauts s) = heavy_metal_umlauts s := sorry

theorem no_vowels_in_result (s : String) :
  ∀ c ∈ String.toList (heavy_metal_umlauts s),
  c ∉ ['A', 'E', 'I', 'O', 'U', 'Y', 'a', 'e', 'i', 'o', 'u', 'y'] := sorry
-- </vc-theorems>