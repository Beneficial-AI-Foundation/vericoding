-- <vc-preamble>
partial def IntValues (n : Int) : Array Int :=
if n = 0 then #[]
else #[n] ++ IntValues (n/10)

def Power10 (n : Nat) : Nat :=
if n = 0 then 1 else 10 * Power10 (n-1)

partial def NumberToSeq (number : Int) : Array Int :=
if number = 0 then #[]
else #[number % 10] ++ NumberToSeq (number/10)

partial def Sum_ (digits : Array Int) : Int :=
if digits.size = 0 then 0
else digits[0]! + Sum_ (digits.extract 1 digits.size)

def NumberOfDigits (n : Nat) : Nat :=
if n ≤ 9 then 1 else 1 + NumberOfDigits (n/10)

def SumDigitsRecursive (n : Nat) (p : Nat) : Nat :=
if n = 0 ∨ p = 0 then 0
else
let leftMostDigit := n/p
let rest := n%p
leftMostDigit + SumDigitsRecursive rest (p/10)

def SumDigits (n : Nat) : Nat :=
let ndigits := NumberOfDigits n
let p := Power10 (ndigits-1)
SumDigitsRecursive n p
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SumOfDigits (number : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IntValues_spec (n : Int) :
n ≥ 0 →
(0 ∈ IntValues n) ∧
(n ∈ IntValues n) ∧
(n/10 ∈ IntValues n) :=
sorry

theorem Power10_spec (n : Nat) :
Power10 n ≥ 1 ∧
(n > 0 → Power10 n % 10 = 0) :=
sorry

theorem NumberOfDigits_spec (n : Nat) :
NumberOfDigits n ≥ 1 ∧
(NumberOfDigits n = 1 ↔ 0 ≤ n ∧ n ≤ 9) :=
sorry

theorem SumOfDigits_spec (number : Nat) :
number ≥ 0 →
SumOfDigits number ≥ 0 ∧
SumOfDigits number = SumDigits number :=
sorry
-- </vc-theorems>