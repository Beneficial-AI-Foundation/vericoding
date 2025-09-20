-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_nice (s: List Char) : Bool :=
  sorry

def count_nice_strings (s: List Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_nice_strings_non_negative (s: List Char) :
  count_nice_strings s ≥ 0 :=
sorry

theorem count_nice_strings_upper_bound (s: List Char) :
  count_nice_strings s ≤ (s.length * (s.length + 1)) / 2 :=
sorry

theorem empty_string_has_zero_nice (s: List Char) :
  s.length = 0 → count_nice_strings s = 0 :=
sorry

theorem is_nice_min_length (s: List Char) :
  is_nice s → s.length ≥ 2 :=
sorry

theorem small_strings_not_nice (s: List Char) :
  s.length ≤ 1 → ¬(is_nice s) :=
sorry

theorem nice_string_conditions (s: List Char) (i: Nat) :
  is_nice s →
  (∀ i, i < s.length → s.get! 0 = s.get! i) ∨
  (∀ i, i > 0 → i < s.length → Char.toNat (s.get! i) > Char.toNat (s.get! (i-1))) ∨
  (∀ i, i > 0 → i < s.length → Char.toNat (s.get! i) < Char.toNat (s.get! (i-1))) :=
sorry

theorem nice_string_has_nice_count (s: List Char) :
  s.length ≥ 2 →
  is_nice s →
  count_nice_strings s ≥ 1 :=
sorry

theorem count_matches_actual_nice (s: List Char) :
  count_nice_strings s =
    (List.foldl (fun acc i =>
      acc + List.foldl (fun inner_acc j =>
        if is_nice (List.take (j + 1) (List.drop i s))
        then inner_acc + 1
        else inner_acc)
      0 (List.range (s.length - i)))
    0 (List.range s.length)) :=
sorry
-- </vc-theorems>