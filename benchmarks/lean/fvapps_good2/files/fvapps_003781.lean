-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def discover_original_price (price : Float) (percentage : Float) : Float :=
sorry

def abs (x : Float) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem discover_original_price_geq_discounted (price : Float) (percentage : Float)
  (h1 : 0 < price) (h2 : 0 < percentage) (h3 : percentage < 100) :
  discover_original_price price percentage ≥ price :=
sorry

theorem discover_original_price_positive (price : Float) (percentage : Float)
  (h1 : 0 < price) (h2 : 0 < percentage) (h3 : percentage < 100) :
  0 < discover_original_price price percentage :=
sorry

theorem discover_original_price_accurate (price : Float) (percentage : Float)
  (h1 : 0 < price) (h2 : 0 < percentage) (h3 : percentage < 100) :
  let original := discover_original_price price percentage
  let discounted := original * (1 - percentage/100)
  Float.abs (discounted - price) ≤ 0.02 :=
sorry

theorem discover_original_price_100_dollars (percentage : Float)
  (h1 : 0 < percentage) (h2 : percentage < 100) :
  let discounted := 100 * (1 - percentage/100)
  Float.abs (discover_original_price discounted percentage - 100) < 0.01 :=
sorry
-- </vc-theorems>