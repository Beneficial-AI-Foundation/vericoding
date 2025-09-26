-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diamonds_and_toads (text: String) (fairy: String) : List (String × Nat) :=
  sorry

/- For good fairies, diamonds_and_toads returns list with keys "ruby" and "crystal" -/
-- </vc-definitions>

-- <vc-theorems>
theorem good_fairy_keys (text: String) :
  let result := diamonds_and_toads text "good"
  List.length result = 2 ∧
  List.elem ("ruby", 0) result ∧
  List.elem ("crystal", 0) result := sorry

/- For evil fairies, diamonds_and_toads returns list with keys "python" and "squirrel" -/

theorem evil_fairy_keys (text: String) :
  let result := diamonds_and_toads text "evil"
  List.length result = 2 ∧
  List.elem ("python", 0) result ∧
  List.elem ("squirrel", 0) result := sorry

/- All values in result list are non-negative -/

theorem non_negative_values (text: String) (fairy: String) :
  let result := diamonds_and_toads text fairy
  ∀ p, p ∈ result → p.2 ≥ 0 := sorry

/- Count in result matches character occurrences with case sensitivity -/

theorem count_matches_occurrences (text: String) (fairy: String) (word: String) (c: Char) :
  let result := diamonds_and_toads text fairy
  ∀ p ∈ result, p.1 = word →
    p.2 = (text.data.filter (· = c)).length + 
          2 * (text.data.filter (· = c.toUpper)).length := sorry

/- Good and evil fairies produce different key sets for same input -/

theorem good_evil_different_keys (text: String) :
  let good_result := diamonds_and_toads text "good"
  let evil_result := diamonds_and_toads text "evil"
  ∀ p₁ ∈ good_result, ∀ p₂ ∈ evil_result, p₁.1 ≠ p₂.1 := sorry

/- Empty string input with good fairy produces pairs with zero counts -/

theorem empty_string_good_fairy :
  diamonds_and_toads "" "good" = [("ruby", 0), ("crystal", 0)] := sorry
-- </vc-theorems>