-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MajorityChecker.query (checker : MajorityChecker) (left right threshold : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem queries_within_array_bounds 
  (arr : IntArray) 
  (left right threshold : Nat)
  (checker : MajorityChecker)
  (h1 : checker.arr = arr)
  (h2 : left ≤ right)
  (h3 : right < arr.length)
  (result : Int)
  (h4 : result = checker.query left right threshold)
  (h5 : result ≠ -1) :
  (List.countP (fun x => x = result) (List.take (right - left + 1) (List.drop left arr))) ≥ threshold := 
  sorry

theorem monotonic_threshold 
  (arr : IntArray)
  (left right threshold1 threshold2 : Nat) 
  (checker : MajorityChecker)
  (h1 : checker.arr = arr)
  (h2 : left ≤ right)
  (h3 : right < arr.length)
  (h4 : threshold1 ≤ threshold2)
  (h5 : threshold2 ≤ right - left + 1)
  (result2 : Int)
  (h6 : result2 = checker.query left right threshold2)
  (h7 : result2 ≠ -1) :
  ∃ result1, 
    result1 = checker.query left right threshold1 ∧
    result1 ≠ -1 := 
  sorry
-- </vc-theorems>