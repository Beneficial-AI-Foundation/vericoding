-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getAllPrimeFactors (n : Int) : List Int :=
sorry

def getUniquePrimeFactorsWithCount (n : Int) : List (List Int) :=
sorry

def getUniquePrimeFactorsWithProducts (n : Int) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prime_factors_product_equals_input {n : Int} (h : 0 ≤ n) :
  let factors := getAllPrimeFactors n
  factors ≠ [] → factors.foldl (·*·) 1 = n :=
sorry

theorem prime_factors_are_ordered {n : Int} (h : 0 ≤ n) :
  let factors := getAllPrimeFactors n
  factors.length > 1 →
  ∀ i : Fin (factors.length - 1), factors[i] ≤ factors[i.val + 1] :=
sorry

theorem negative_inputs {n : Int} (h : n < 0) :
  getAllPrimeFactors n = [] ∧
  getUniquePrimeFactorsWithCount n = [[], []] ∧
  getUniquePrimeFactorsWithProducts n = [] :=
sorry

theorem count_matches_occurrences {n : Int} (h : 0 ≤ n) :
  let factors := getAllPrimeFactors n
  let uniqueWithCount := getUniquePrimeFactorsWithCount n
  factors ≠ [] →
  ∀ (p c : Int),
  List.zip uniqueWithCount[0]! uniqueWithCount[1]! |>.contains (p, c) →
  (factors.filter (·= p)).length = c :=
sorry

theorem products_match_prime_power {n : Int} (h : 0 ≤ n) :
  let uniqueWithCount := getUniquePrimeFactorsWithCount n
  let products := getUniquePrimeFactorsWithProducts n
  uniqueWithCount[0]! ≠ [] →
  products.length = uniqueWithCount[0]!.length ∧
  ∀ (p c prod : Int),
  List.zip (List.zip uniqueWithCount[0]! uniqueWithCount[1]!) products |>.contains ((p, c), prod) →
  prod = p * c :=
sorry

theorem edge_cases :
  getAllPrimeFactors 0 = [] ∧
  getUniquePrimeFactorsWithCount 0 = [[], []] ∧
  getUniquePrimeFactorsWithProducts 0 = [] ∧
  getAllPrimeFactors 1 = [1] ∧
  getUniquePrimeFactorsWithCount 1 = [[1], [1]] ∧
  getUniquePrimeFactorsWithProducts 1 = [1] :=
sorry
-- </vc-theorems>