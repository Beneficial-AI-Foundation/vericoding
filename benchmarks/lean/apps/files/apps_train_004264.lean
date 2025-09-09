-- <vc-helpers>
-- </vc-helpers>

def solution (s : String) : Nat := sorry

def isValidRoman (s : String) : Bool := sorry

theorem single_repeated_numerals {roman : String} (c : Char)
  (h1 : roman.data.all (· = c))
  (h2 : c ∈ ['M', 'D', 'C', 'L', 'X', 'V', 'I']) :
  solution roman = solution (toString c) * roman.length := sorry

theorem subtractive_pairs_less :
  solution "IV" < solution "VI" ∧
  solution "IX" < solution "XI" ∧ 
  solution "XL" < solution "LX" ∧
  solution "XC" < solution "CX" ∧
  solution "CD" < solution "DC" ∧
  solution "CM" < solution "MC" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible