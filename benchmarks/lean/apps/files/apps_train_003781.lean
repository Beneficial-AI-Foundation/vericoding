/-
We need to write some code to return the original price of a product, the return type must be of type decimal and the number must be rounded to two decimal places.

We will be given the sale price (discounted price), and the sale percentage, our job is to figure out the original price.

### For example:

Given an item at $75 sale price after applying a 25% discount, the function should return the original price of that item before applying the sale percentage, which is ($100.00) of course, rounded to two decimal places.

DiscoverOriginalPrice(75, 25) => 100.00M where 75 is the sale price (discounted price), 25 is the sale percentage and 100 is the original price
-/

def discover_original_price (price : Float) (percentage : Float) : Float :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def abs (x : Float) : Float :=
sorry

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

/-
info: Decimal('100.00')
-/
-- #guard_msgs in
-- #eval discover_original_price 75 25

/-
info: Decimal('100.00')
-/
-- #guard_msgs in
-- #eval discover_original_price 25 75

/-
info: Decimal('421.00')
-/
-- #guard_msgs in
-- #eval discover_original_price 373.85 11.2

-- Apps difficulty: introductory
-- Assurance level: unguarded