-- <vc-preamble>
def count_distinct_names (words: List String) : Nat := sorry

theorem count_distinct_names_bounded (words: List String) (h: words ≠ []) :
  let result := count_distinct_names words
  result ≤ words.length ∧ result ≥ 1 := sorry

/- Helper function to process a string by replacing kh sequences -/

def processKh (s: String) : String := sorry

/- Helper function to process a string by replacing u with oo -/

def processU (s: String) : String := sorry

/- Helper function to fully process a string with all replacements -/
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def processString (s: String) : String := processKh (processU s)

def unique {α} [BEq α] (l: List α) : List α :=
  l.foldl (fun acc x => if acc.elem x then acc else x :: acc) []
-- </vc-definitions>

-- <vc-theorems>
/-
info: 4
-/
-- #guard_msgs in
-- #eval count_distinct_names ["mihail", "oolyana", "kooooper", "hoon", "ulyana", "koouper", "mikhail", "khun", "kuooper", "kkkhoon"]

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_distinct_names ["hariton", "hkariton", "buoi", "kkkhariton", "boooi", "bui", "khariton", "boui", "boi"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_distinct_names ["alex", "alex"]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible