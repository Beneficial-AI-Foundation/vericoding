-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_pangram_cost (prices : List Nat) (text : String) : Nat := sorry

theorem pangram_cost_nonnegative (prices : List Nat) (text : String) 
    (h : prices.length = 26) : 
  get_pangram_cost prices text ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pangram_cost_empty_string (prices : List Nat)
    (h : prices.length = 26) :
  get_pangram_cost prices "" = prices.foldl (·+·) 0 := sorry
-- </vc-theorems>