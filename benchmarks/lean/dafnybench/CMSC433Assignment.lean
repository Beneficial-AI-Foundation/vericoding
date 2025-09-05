/-
  Port of cmsc433_tmp_tmpe3ob3a0o_dafny_project1_p1-assignment-2_spec.dfy
  
  This specification contains multiple verification problems from a CMSC 433 assignment:
  - PlusOne: Increment a non-negative integer
  - Swap: Swap two elements in an array
  - IntDiv: Integer division with remainder
  - ArraySum: Element-wise sum of two arrays
  - Euclid: Greatest common divisor
  - IsSorted: Check if array is sorted
  - IsPrime: Check if a number is prime
  - Reverse: Reverse an array
  - NoDups: Check for no duplicates in sorted array
-/

namespace DafnyBenchmarks

/-- Question 1: Increment a non-negative integer -/
def plusOne (x : Int) : Int := sorry

theorem plusOne_spec (x : Int) 
    (h : x ≥ 0) :
    plusOne x > 0 := by
  sorry

/-- Question 2: Swap two elements in an array -/
def swap (a : Array Int) (i j : Nat) : Array Int := sorry

theorem swap_spec (a : Array Int) (i j : Nat) 
    (h : 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size) :
    let result := swap a i j
    result[i]! = a[j]! ∧ result[j]! = a[i]! := by
  sorry

/-- Question 3: Integer division with remainder -/
def intDiv (m n : Int) : Int × Int := sorry

theorem intDiv_spec (m n : Int) 
    (h : n > 0) :
    let (d, r) := intDiv m n
    m = n * d + r ∧ 0 ≤ r ∧ r < n := by
  sorry

/-- Question 4: Element-wise sum of two arrays -/
def arraySum (a b : Array Int) : Array Int := sorry

theorem arraySum_spec (a b : Array Int) 
    (h : a.size = b.size) :
    let c := arraySum a b
    c.size = a.size ∧ 
    ∀ i, 0 ≤ i ∧ i < c.size → c[i]! = a[i]! + b[i]! := by
  sorry

/-- Question 5: Euclid's algorithm for GCD -/
def euclid (m n : Nat) : Nat := sorry
termination_by n

theorem euclid_spec (m n : Nat) 
    (h : m > 1 ∧ n > 1 ∧ m ≥ n) :
    let gcd := euclid m n
    gcd > 0 ∧ gcd ≤ n ∧ gcd ≤ m ∧ m % gcd = 0 ∧ n % gcd = 0 := by
  sorry

/-- Question 6: Check if array is sorted -/
def isSorted (a : Array Int) : Bool := sorry

theorem isSorted_spec (a : Array Int) :
    isSorted a ↔ ∀ j, 1 ≤ j ∧ j < a.size → a[j - 1]! ≤ a[j]! := by
  sorry

/-- Question 7: Check if a number is prime -/
def isPrime (m : Nat) : Bool := sorry

theorem isPrime_spec (m : Nat) 
    (h : m > 0) :
    isPrime m ↔ (m > 1 ∧ ∀ j, 2 ≤ j ∧ j < m → m % j ≠ 0) := by
  sorry

/-- Question 8: Reverse an array -/
def reverse (a : Array Int) : Array Int := sorry

theorem reverse_spec (a : Array Int) :
    let aRev := reverse a
    aRev.size = a.size ∧ 
    ∀ i, 0 ≤ i ∧ i < a.size → a[i]! = aRev[aRev.size - i - 1]! := by
  sorry

/-- Question 9: Check for no duplicates in sorted array -/
def noDups (a : Array Int) : Bool := sorry

theorem noDups_spec (a : Array Int) 
    (h : ∀ j, 0 < j ∧ j < a.size → a[j - 1]! ≤ a[j]!) :
    noDups a ↔ ∀ j, 1 ≤ j ∧ j < a.size → a[j - 1]! ≠ a[j]! := by
  sorry

end DafnyBenchmarks
