-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_value (digits : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_value_is_nat (digits : List Nat) :
  min_value digits > 0 :=
  sorry

theorem min_value_digits_unique (digits : List Nat) :
  let result := min_value digits
  let resultDigits := result.repr.toList
  List.Nodup resultDigits :=
  sorry

theorem min_value_subset (digits : List Nat) :
  let result := min_value digits 
  let resultDigits := result.repr.toList
  ∀ d ∈ resultDigits, ∃ n ∈ digits, toString n = toString d :=
  sorry

theorem min_value_ascending (digits : List Nat) :
  let result := min_value digits
  let resultDigits := result.repr.toList
  ∀ (i j : Fin resultDigits.length), 
    i.val < j.val → resultDigits[i] ≤ resultDigits[j] :=
  sorry

theorem min_value_equals_sorted_unique (digits : List Nat) :
  min_value digits = 
    String.toNat! (String.join (List.map Nat.repr (List.eraseDups digits))) :=
  sorry
-- </vc-theorems>