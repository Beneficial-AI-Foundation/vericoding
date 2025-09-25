-- <vc-preamble>
def numWordsList := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]

def sum (l : List Nat) : Nat := l.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numToWord (n : Nat) : String :=
sorry

def wordToNum (s : String) : Option Nat :=
sorry

def average_string (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem average_string_valid_nums (words : List String)
  (h : ∀ w ∈ words, w ∈ numWordsList) (h2 : words ≠ []) :
  let nums := words.filterMap wordToNum
  let avg := sum nums / nums.length
  average_string (String.intercalate " " words) = numToWord avg :=
sorry

theorem average_string_empty :
  average_string "" = "n/a" :=
sorry

theorem average_string_invalid (s : String)
  (h : ∃ w ∈ s.split (· = ' '), w ∉ numWordsList) :
  average_string s = "n/a" :=
sorry
-- </vc-theorems>