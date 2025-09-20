-- <vc-preamble>
def sumList : List Nat → Nat
  | [] => 0
  | x::xs => x + sumList xs

def isSorted : List String → Bool
  | [] => true
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countDigits (a b : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem countDigits_format_valid {a b : Nat} (h : a ≤ b) (n : Nat) (h1 : n < 10^4) :
  let result := countDigits a b
  let pairs := (result.split (· = ' '))
  pairs.length = 10 ∧
  (∀ p ∈ pairs, ∃ d c, (p.split (· = ':')) = [d, c] ∧
     d ∈ ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] ∧
     (∀ ch ∈ c.data, ch.isDigit)) ∧
  isSorted (pairs.map (fun p => ((p.split (· = ':')).get! 0))) :=
sorry

theorem countDigits_count_valid {a b : Nat} (h : a ≤ b) :
  let result := countDigits a b
  let counts := ((result.split (· = ' ')).map
    (fun p => String.toNat! ((p.split (· = ':')).get! 1)))
  let digitCount := (List.range (b - a + 1)).map
    (fun i => (toString (i + a)).length)
  sumList counts = sumList digitCount :=
sorry

theorem countDigits_single_num_valid (n : Nat) :
  let result := countDigits n n
  let counts := ((result.split (· = ' ')).map
    (fun p => String.toNat! ((p.split (· = ':')).get! 1)))
  ∀ d : Nat, d < 10 →
    (counts.get! d) = ((toString n).data.filter
      (fun c => c = (toString d).data.get! 0)).length :=
sorry
-- </vc-theorems>