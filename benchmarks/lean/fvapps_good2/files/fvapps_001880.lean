-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shoppingOffers (price : List Int) (special : List (List Int)) (needs : List Int) : Int :=
  sorry

def isValidInput (price : List Int) (special : List (List Int)) (needs : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shoppingOffers_result_nonnegative
  (price : List Int) (special : List (List Int)) (needs : List Int)
  (h_price : ∀ p ∈ price, 1 ≤ p ∧ p ≤ 10)
  (h_special : ∀ s ∈ special, ∀ x ∈ s, 0 ≤ x ∧ x ≤ 10)
  (h_needs : ∀ n ∈ needs, 0 ≤ n ∧ n ≤ 10)
  (h_valid : isValidInput price special needs) :
  0 ≤ shoppingOffers price special needs :=
sorry

theorem shoppingOffers_not_exceed_list_price
  (price : List Int) (special : List (List Int)) (needs : List Int)
  (h_price : ∀ p ∈ price, 1 ≤ p ∧ p ≤ 10)
  (h_special : ∀ s ∈ special, ∀ x ∈ s, 0 ≤ x ∧ x ≤ 10)
  (h_needs : ∀ n ∈ needs, 0 ≤ n ∧ n ≤ 10)
  (h_valid : isValidInput price special needs) :
  shoppingOffers price special needs ≤ (List.zip price needs).foldl (fun acc (p, n) => acc + p * n) 0 :=
sorry

theorem shoppingOffers_no_special_equals_list_price
  (price : List Int) (needs : List Int)
  (h_price : ∀ p ∈ price, 1 ≤ p ∧ p ≤ 5)
  (h_needs : ∀ n ∈ needs, 0 ≤ n ∧ n ≤ 5)
  (h_valid : isValidInput price [] needs) :
  shoppingOffers price [] needs = (List.zip price needs).foldl (fun acc (p, n) => acc + p * n) 0 :=
sorry
-- </vc-theorems>