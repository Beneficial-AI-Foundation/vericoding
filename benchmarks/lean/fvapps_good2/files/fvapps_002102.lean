-- <vc-preamble>
def unique {α} [BEq α] (l: List α) : List α :=
  l.foldl (fun acc x => if acc.elem x then acc else x :: acc) []
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_distinct_names (words: List String) : Nat :=
sorry

def processKh (s: String) : String :=
sorry

def processU (s: String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def processString (s: String) : String := processKh (processU s)

theorem count_distinct_names_bounded (words: List String) (h: words ≠ []) :
  let result := count_distinct_names words
  result ≤ words.length ∧ result ≥ 1 :=
sorry
-- </vc-theorems>