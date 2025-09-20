-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum (l : List Int) : Int := sorry

def slidemax (nums : List Int) (k : Nat) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem slidemax_matches_window_max
  (nums : List Int) (k : Nat)
  (h1 : 0 < k) 
  (h2 : k ≤ nums.length) :
  slidemax nums k = 
    (List.range (nums.length + 1 - k)).map (fun i =>
      maximum (List.take k (List.drop i nums))) := sorry

theorem slidemax_length
  (nums : List Int) (k : Nat)
  (h1 : 0 < k)
  (h2 : k ≤ nums.length) :
  (slidemax nums k).length = nums.length + 1 - k := sorry
-- </vc-theorems>