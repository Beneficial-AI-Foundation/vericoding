def isAlpha (c : Char) : Bool :=
  sorry

def swap (s : String) (n : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def swapcase (c : Char) : Char :=
  sorry

theorem swap_length_preserved (s : String) (n : Nat) :
  (swap s n).length = s.length :=
sorry

theorem swap_nonalpha_preserved (s : String) (n : Nat) (pos : String.Pos) :
  ¬isAlpha (s.get pos) → (swap s n).get pos = s.get pos :=
sorry

theorem swap_alpha_case (s : String) (n : Nat) (pos : String.Pos) :
  isAlpha (s.get pos) → 
  (s.get pos).toLower = ((swap s n).get pos).toLower :=
sorry

theorem swap_zero_identity (s : String) :
  swap s 0 = s :=
sorry

theorem swap_pattern_matches_binary (s : String) (n : Nat) (pos : String.Pos) 
    (binPattern : String) (idx : String.Pos) :
  isAlpha (s.get pos) →
  binPattern = (toString n).dropWhile (· = '0') →
  (binPattern.get idx = '1' → 
    (swap s n).get pos = swapcase (s.get pos)) ∧
  (binPattern.get idx = '0' → 
    (swap s n).get pos = s.get pos) :=
sorry

/-
info: 'heLLO wORLd!'
-/
-- #guard_msgs in
-- #eval swap "Hello world!" 11

/-
info: 'GooD MorNIng'
-/
-- #guard_msgs in
-- #eval swap "gOOd MOrniNg" 7864

/-
info: 'the lord of the rings'
-/
-- #guard_msgs in
-- #eval swap "the lord of the rings" 0

-- Apps difficulty: introductory
-- Assurance level: unguarded