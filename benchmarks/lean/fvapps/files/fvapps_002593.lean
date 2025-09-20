-- <vc-preamble>
def splitLines (s : String) : List String :=
  String.splitOn s "\n"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isqrt (n : Nat) : Nat := sorry

def squareIt (n : Nat) : String :=
sorry

def isPerfectSquare (n : Nat) : Bool :=
sorry

def hasEqualRows (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_it_properties (n : Nat) :
  n ≤ 10^12 →
  let digits := toString n
  if isPerfectSquare (digits.length) then
    let result := squareIt n
    result ≠ "Not a perfect square!" ∧
    hasEqualRows result ∧
    let sideLength := isqrt (digits.length)
    (splitLines result).length = sideLength ∧
    (∀ row ∈ splitLines result, row.length = sideLength) ∧
    String.join (splitLines result) = digits
  else
    squareIt n = "Not a perfect square!"
  :=
sorry

theorem square_it_repeating_ones (n : Nat) (k : Nat) :
  k ≥ 1 →
  k ≤ 4 →
  n = (10^(k*k) - 1)/9 →
  let result := squareIt n
  result ≠ "Not a perfect square!" ∧
  let rows := splitLines result
  ∀ row ∈ rows, match rows.head? with
                | none => True
                | some first => row = first
  :=
sorry
-- </vc-theorems>