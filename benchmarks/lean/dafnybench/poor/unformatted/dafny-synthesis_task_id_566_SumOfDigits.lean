

/-!
{
"name": "dafny-synthesis_task_id_566_SumOfDigits",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_566_SumOfDigits",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Recursive function that returns sequence of intermediate values when dividing by 10 -/
partial def IntValues (n : Int) : Array Int :=
if n = 0 then #[]
else #[n] ++ IntValues (n/10)

theorem IntValues_spec (n : Int) :
n ≥ 0 →
(0 ∈ IntValues n) ∧
(n ∈ IntValues n) ∧
(n/10 ∈ IntValues n) := sorry

/-- Computes powers of 10 -/
def Power10 (n : Nat) : Nat :=
if n = 0 then 1 else 10 * Power10 (n-1)

theorem Power10_spec (n : Nat) :
Power10 n ≥ 1 ∧
(n > 0 → Power10 n % 10 = 0) := sorry

/-- Converts a number to sequence of its digits -/
partial def NumberToSeq (number : Int) : Array Int :=
if number = 0 then #[]
else #[number % 10] ++ NumberToSeq (number/10)

/-- Sums elements in a sequence -/
partial def Sum (digits : Array Int) : Int :=
if digits.size = 0 then 0
else digits[0]! + Sum (digits.extract 1 digits.size)

/-- Counts number of digits in a natural number -/
def NumberOfDigits (n : Nat) : Nat :=
if n ≤ 9 then 1 else 1 + NumberOfDigits (n/10)

theorem NumberOfDigits_spec (n : Nat) :
NumberOfDigits n ≥ 1 ∧
(NumberOfDigits n = 1 ↔ 0 ≤ n ∧ n ≤ 9) := sorry

/-- Recursively sums digits using powers of 10 -/
def SumDigitsRecursive (n : Nat) (p : Nat) : Nat :=
if n = 0 ∨ p = 0 then 0
else
let leftMostDigit := n/p
let rest := n%p
leftMostDigit + SumDigitsRecursive rest (p/10)

/-- Main function to sum digits of a number -/
def SumDigits (n : Nat) : Nat :=
let ndigits := NumberOfDigits n
let p := Power10 (ndigits-1)
SumDigitsRecursive n p

/-- Main method specification -/
def SumOfDigits (number : Nat) : Nat := sorry

theorem SumOfDigits_spec (number : Nat) :
number ≥ 0 →
SumOfDigits number ≥ 0 ∧
SumOfDigits number = SumDigits number := sorry
