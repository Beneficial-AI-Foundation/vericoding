-- <vc-preamble>
def minPointsForStringConversion (s : String) : Nat := sorry

theorem minPoints_nonNegative (s : String) (h : s.length > 0) : 
  minPointsForStringConversion s ≥ 0 := sorry

def allSameChar (s : String) : Bool := sorry 

theorem minPoints_zero_for_same_chars (s : String) (h1 : s.length > 0) (h2 : allSameChar s = true) :
  minPointsForStringConversion s = 0 := sorry

def minCharOfString (s : String) : Char := sorry
def maxCharOfString (s : String) : Char := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def naiveLowerBound (s : String) : Nat :=
  let minChar := minCharOfString s
  let maxChar := maxCharOfString s
  min 
    (s.data.foldl (fun acc c => acc + (c.toNat - minChar.toNat)) 0)
    (s.data.foldl (fun acc c => acc + (c.toNat - maxChar.toNat)) 0)
-- </vc-definitions>

-- <vc-theorems>
theorem minPoints_upper_bound (s : String) (h : s.length > 0) :
  minPointsForStringConversion s ≤ s.length * (('z'.toNat) - ('a'.toNat)) := sorry

theorem minPoints_repeated_string (s : String) (h : s.length > 0) :
  minPointsForStringConversion (s ++ s) = 2 * minPointsForStringConversion s := sorry

theorem minPoints_naive_bound (s : String) (h : s.length > 0) :
  minPointsForStringConversion s ≤ naiveLowerBound s := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_points_for_string_conversion "abba"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_points_for_string_conversion "a"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_points_for_string_conversion "zzz"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded