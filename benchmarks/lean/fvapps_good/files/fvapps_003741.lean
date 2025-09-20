-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) : Int := sorry

def bills : List Int := [500, 200, 100, 50, 20, 10]
-- </vc-definitions>

-- <vc-theorems>
theorem solve_spec (n : Int) (h : n > 0) (h2 : n ≤ 10^6) :
  let result := solve n
  if n % 10 ≠ 0 then
    result = -1
  else
    result ≥ 0 ∧ 
    result ≤ n / 10 ∧
    ∃ (count : Int) (remaining : Int) (reconstructed : Int),
      count = result ∧
      reconstructed + remaining = n ∧
      (∀ bill ∈ bills,
        ∃ (num_bills : Int) (remaining' : Int),
          remaining = bill * num_bills + remaining' ∧
          remaining' < bill ∧
          count ≥ 0) := sorry

theorem solve_optimal (n : Int) (h : n > 0) (h2 : n ≤ 10^6) (h3 : n % 10 = 0) :
  let result := solve n
  result > 0 ∧ 
  ∀ (count : Int) (total : Int) (remaining : Int),
    (∀ bill ∈ bills,
      ∃ (num_bills : Int) (remaining' : Int),
        remaining = bill * num_bills + remaining' ∧
        remaining' < bill ∧
        count = result) →
    result ≤ count := sorry
-- </vc-theorems>