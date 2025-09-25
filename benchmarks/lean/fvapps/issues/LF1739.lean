-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def StockSpanner.next (self : StockSpanner) (price : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spanner_spans_positive (prices : List Nat) :
  let spanner : StockSpanner := default
  let spans := prices.map (StockSpanner.next spanner)
  ∀ span ∈ spans, span > 0 :=
sorry

theorem spanner_spans_bounded (prices : List Nat) :
  let spanner : StockSpanner := default
  let spans := prices.map (StockSpanner.next spanner)
  ∀ (i : Nat), i < spans.length → spans[i]! ≤ i + 1 :=
sorry

theorem spanner_repeated_prices (n : Nat) (price : Nat) :
  let spanner : StockSpanner := default
  let prices := List.replicate n price
  let spans := prices.map (StockSpanner.next spanner)
  ∀ (i : Nat), i < spans.length → spans[i]! = i + 1 :=
sorry
-- </vc-theorems>