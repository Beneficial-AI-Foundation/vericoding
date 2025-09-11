-- <vc-preamble>
def countDigits (a b : Nat) : String := sorry

def sumList : List Nat → Nat 
  | [] => 0
  | x::xs => x + sumList xs
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted : List String → Bool
  | [] => true
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)
-- </vc-definitions>

-- <vc-theorems>
theorem countDigits_format_valid {a b : Nat} (h : a ≤ b) (n : Nat) (h1 : n < 10^4) :
  let result := countDigits a b
  let pairs := (result.split (· = ' '))
  pairs.length = 10 ∧
  (∀ p ∈ pairs, ∃ d c, (p.split (· = ':')) = [d, c] ∧ 
     d ∈ ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] ∧
     (∀ ch ∈ c.data, ch.isDigit)) ∧
  isSorted (pairs.map (fun p => ((p.split (· = ':')).get! 0))) := sorry

theorem countDigits_count_valid {a b : Nat} (h : a ≤ b) :
  let result := countDigits a b
  let counts := ((result.split (· = ' ')).map 
    (fun p => String.toNat! ((p.split (· = ':')).get! 1)))
  let digitCount := (List.range (b - a + 1)).map 
    (fun i => (toString (i + a)).length)
  sumList counts = sumList digitCount := sorry

theorem countDigits_single_num_valid (n : Nat) :
  let result := countDigits n n
  let counts := ((result.split (· = ' ')).map 
    (fun p => String.toNat! ((p.split (· = ':')).get! 1)))
  ∀ d : Nat, d < 10 →
    (counts.get! d) = ((toString n).data.filter 
      (fun c => c = (toString d).data.get! 0)).length := sorry

/-
info: '0:1 1:7 2:1 3:1 4:1 5:1 6:0 7:0 8:0 9:0'
-/
-- #guard_msgs in
-- #eval count_digits 10 15

/-
info: '0:0 1:1 2:1 3:0 4:0 5:0 6:0 7:0 8:0 9:1'
-/
-- #guard_msgs in
-- #eval count_digits 912 912

/-
info: '0:20 1:20 2:20 3:20 4:20 5:20 6:20 7:20 8:20 9:120'
-/
-- #guard_msgs in
-- #eval count_digits 900 999
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded