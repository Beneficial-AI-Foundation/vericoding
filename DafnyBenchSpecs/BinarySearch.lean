/-
  Port of 630-dafny_tmp_tmpz2kokaiq_Solution_spec.dfy
  
  This specification describes a binary search algorithm:
  - Takes a sorted array and a value to search for
  - Returns the index of the value if found
  - Returns -1 if the value is not in the array
-/

namespace DafnyBenchmarks

/-- Predicate to check if an array is sorted -/
def sorted (a : Array Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!

/-- Binary search implementation -/
def binarySearch (a : Array Int) (x : Int) : Int :=
  let rec search (low high : Nat) : Int :=
    if low > high then -1
    else
      let mid := (low + high) / 2
      if h : mid < a.size then
        if a[mid] = x then mid
        else if a[mid] < x then search (mid + 1) high
        else 
          if mid = 0 then -1
          else search low (mid - 1)
      else -1
  termination_by high + 1 - low
  decreasing_by
    all_goals simp_wf
    · omega
    · omega
  search 0 (a.size - 1)

/-- Specification for binarySearch -/
theorem binarySearch_spec (a : Array Int) (x : Int) 
    (h : sorted a) :
    let index := binarySearch a x
    (0 ≤ index ∧ index < a.size → a[index.toNat]! = x) ∧
    (index = -1 → ∀ i, 0 ≤ i ∧ i < a.size → a[i]! ≠ x) := by
  sorry

end DafnyBenchmarks