/-
Binary search variations including Search1000 and power-of-2 searches.
Ported from Dafny specification at:
dafny/benchmarks/dafny-bench_specs/atomizer_supported/Dafny_tmp_tmp0wu8wmfr_tests_Search1000_spec.dfy

This module contains specifications for binary search on arrays,
including a specific version for arrays of size at least 1000,
and versions that work on array segments of size 2^k - 1.
-/

namespace DafnyBenchmarks

/-- Binary search on first 1000 elements of an array -/
def search1000 (a : Array Int) (x : Int) : Nat :=
  let rec searchLoop (low high : Nat) : Nat :=
    if low > high then low
    else
      let mid := (low + high) / 2
      if h : mid < a.size ∧ mid < 1000 then
        if a[mid] < x then
          searchLoop (mid + 1) high
        else
          searchLoop low (mid - 1)
      else low
  termination_by high - low
  searchLoop 0 999

/-- Predicate to check if n is a power of 2 -/
def is2Pow : Nat → Bool
  | 0 => false
  | 1 => true
  | n => n % 2 = 0 && is2Pow (n / 2)
termination_by n => n
decreasing_by sorry

/-- Binary search using a loop on array segments of size 2^k - 1 -/
def search2PowLoop (a : Array Int) (i n : Nat) (x : Int) : Nat :=
  if n = 0 then i
  else
    let rec searchLoop (low high : Nat) : Nat :=
      if low > high then low
      else
        let mid := (low + high) / 2
        if h : mid < a.size then
          if a[mid] < x then
            searchLoop (mid + 1) high
          else
            searchLoop low (if mid > 0 then mid - 1 else 0)
        else low
    termination_by high - low
    searchLoop i (i + n - 1)

/-- Binary search using recursion on array segments of size 2^k - 1 -/
def search2PowRecursive (a : Array Int) (i n : Nat) (x : Int) : Nat :=
  if n = 0 then i
  else
    let m := n / 2
    let mid := i + m
    if h : mid < a.size then
      if a[mid] < x then
        search2PowRecursive a (mid + 1) (n - m - 1) x
      else
        search2PowRecursive a i m x
    else i
termination_by n - i

/-- Specification for search1000 -/
theorem search1000_spec (a : Array Int) (x : Int)
    (h_size : a.size ≥ 1000)
    (h_sorted : ∀ p q, 0 ≤ p → p < q → q < 1000 → a[p]! ≤ a[q]!) :
    let k := search1000 a x
    0 ≤ k ∧ k ≤ 1000 ∧
    (∀ r, 0 ≤ r → r < k → r < 1000 → a[r]! < x) ∧
    (∀ r, k ≤ r → r < 1000 → a[r]! ≥ x) := by
  sorry

/-- Specification for search2PowLoop -/
theorem search2PowLoop_spec (a : Array Int) (i n : Nat) (x : Int)
    (h_bounds : 0 ≤ i ∧ i + n ≤ a.size)
    (h_sorted : ∀ p q, i ≤ p → p < q → q < i + n → a[p]! ≤ a[q]!)
    (h_pow : is2Pow (n + 1)) :
    let k := search2PowLoop a i n x
    i ≤ k ∧ k ≤ i + n ∧
    (∀ r, i ≤ r → r < k → r < a.size → a[r]! < x) ∧
    (∀ r, k ≤ r → r < i + n → r < a.size → a[r]! ≥ x) := by
  sorry

/-- Specification for search2PowRecursive -/
theorem search2PowRecursive_spec (a : Array Int) (i n : Nat) (x : Int)
    (h_bounds : 0 ≤ i ∧ i + n ≤ a.size)
    (h_sorted : ∀ p q, i ≤ p → p < q → q < i + n → a[p]! ≤ a[q]!)
    (h_pow : is2Pow (n + 1)) :
    let k := search2PowRecursive a i n x
    i ≤ k ∧ k ≤ i + n ∧
    (∀ r, i ≤ r → r < k → r < a.size → a[r]! < x) ∧
    (∀ r, k ≤ r → r < i + n → r < a.size → a[r]! ≥ x) := by
  sorry

end DafnyBenchmarks