-- <vc-preamble>
def count_char (s : String) (c : Char) : Nat :=
  s.foldl (fun acc x => if x = c then acc + 1 else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_ciel_number_prices (menu_items : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_result_bounded (menu_items : List String) :
  0 ≤ count_ciel_number_prices menu_items ∧
  count_ciel_number_prices menu_items ≤ menu_items.length :=
sorry

theorem count_result_bounded_with_format
  (menu_items : List String)
  (h : ∀ item ∈ menu_items, ∃ words price, item = words ++ " " ++ price ∧ price.all (λ c => '0' ≤ c ∧ c ≤ '9')) :
  0 ≤ count_ciel_number_prices menu_items ∧
  count_ciel_number_prices menu_items ≤ menu_items.length :=
sorry

theorem count_ciel_numbers_positive
  (menu_items : List String)
  (h : ∃ item ∈ menu_items,
    let price := (item.split (· = ' ')).getLast!
    price.all (λ c => c = '8' ∨ c = '5' ∨ c = '3') ∧
    count_char price '8' ≥ count_char price '5' ∧
    count_char price '5' ≥ count_char price '3') :
  count_ciel_number_prices menu_items > 0 :=
sorry
-- </vc-theorems>