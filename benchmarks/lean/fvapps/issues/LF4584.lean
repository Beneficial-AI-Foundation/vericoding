-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def char_freq (s : String) : CharFreq := sorry

theorem char_freq_sum_equals_length (s : String) :
  let result := char_freq s
  (List.map (fun c => (result.count c)) s.data).sum = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem char_freq_contains_all_chars (s : String) :
  let result := char_freq s
  ∀ c, c ∈ s.data → result.count c > 0 := sorry

theorem char_freq_positive_counts (s : String) :
  let result := char_freq s
  ∀ c, result.count c > 0 → c ∈ s.data := sorry

theorem char_freq_accurate_counts (s : String) :
  let result := char_freq s
  ∀ c, (s.data.filter (λ x => x = c)).length = result.count c := sorry

theorem char_freq_max_exists (s : String) (h : s.length > 0) :
  let result := char_freq s
  ∃ c ∈ s.data, ∀ d ∈ s.data, result.count c ≥ result.count d := sorry

theorem char_freq_concatenation (s₁ s₂ : String) :
  let result₁ := char_freq s₁
  let result₂ := char_freq s₂
  let result_combined := char_freq (s₁ ++ s₂)
  ∀ c, result_combined.count c = result₁.count c + result₂.count c := sorry

/-
info: {'a': 1, ' ': 2, 'c': 1, 'e': 1, 'I': 1, 'k': 1, 'l': 1, 'i': 1, 's': 1, 't': 1}
-/
-- #guard_msgs in
-- #eval char_freq "I like cats"

/-
info: {'H': 1, 'e': 1, 'l': 2, 'o': 1}
-/
-- #guard_msgs in
-- #eval char_freq "Hello"

/-
info: {'a': 3}
-/
-- #guard_msgs in
-- #eval char_freq "aaa"
-- </vc-theorems>