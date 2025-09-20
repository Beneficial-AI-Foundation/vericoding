-- <vc-preamble>
def listSum (lst : List Int) : Int := lst.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n : Int) : Bool :=
sorry

def primeFactor (n: Int) : List Int :=
sorry

def sumForList (lst : List Int) : List (Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem results_are_prime_factors {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  ∀ pt, pt ∈ sumForList lst →
    isPrime pt.1 = true ∧
    ∃ x, x ∈ lst ∧ x % pt.1 = 0 :=
sorry

theorem sums_are_correct {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  ∀ pt, pt ∈ sumForList lst →
    pt.2 = listSum (lst.filter (fun x => x % pt.1 = 0)) :=
sorry

theorem factors_ordered {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  List.Pairwise (· ≤ ·) (List.map Prod.fst (sumForList lst)) :=
sorry

theorem all_prime_factors_included {lst : List Int} (h : ∀ x, x ∈ lst → x ≠ 0) :
  (∀ p, p ∈ List.map Prod.fst (sumForList lst) →
    (∃ x, x ∈ lst ∧ x % p = 0 ∧ isPrime p = true)) ∧
  (∀ x, x ∈ lst → ∀ p, p ∈ primeFactor x →
    p ∈ List.map Prod.fst (sumForList lst)) :=
sorry
-- </vc-theorems>