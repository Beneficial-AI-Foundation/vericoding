-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_distinct_or_values (nums : List Nat) : Nat := sorry

def uniqueCount (l : List Nat) : Nat := 
  (l.foldl (fun acc x => if x ∈ acc then acc else x::acc) []).length
-- </vc-definitions>

-- <vc-theorems>
theorem count_distinct_or_values_singleton {n : Nat} :
  count_distinct_or_values [n] = 1 := sorry
-- </vc-theorems>