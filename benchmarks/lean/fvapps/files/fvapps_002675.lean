-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String :=
sorry

def String.lines (s : String) : List String :=
sorry

def toString (n : Int) : Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_positive_returns_empty
  (n : Int)
  (h : n ≤ 0) :
  pattern n = "" :=
sorry

theorem output_format_empty
  (n : Int)
  (h : n = 1) :
  pattern n = "" :=
sorry

theorem output_format_content
  (n : Int)
  (h1 : n > 1)
  (h2 : n ≤ 100)
  (i : Nat)
  (h3 : i > 0)
  (h4 : i ≤ n/2) :
  (pattern n).lines.get! (i-1) = String.mk (List.replicate (2*i) (toString (2*i))) :=
sorry

theorem odd_even_equivalence
  (n : Int)
  (h1 : n > 1)
  (h2 : n ≤ 100)
  (h3 : n % 2 = 1) :
  pattern n = pattern (n-1) :=
sorry

theorem line_count
  (n : Int)
  (h1 : n > 1)
  (h2 : n ≤ 100) :
  (pattern n).lines.length = n/2 :=
sorry
-- </vc-theorems>