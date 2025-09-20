-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_merge (s1 s2 : String) (c : Char) : String := sorry

def findIndex (s : String) (c : Char) : Option Nat := sorry

structure StringMergeError where
  msg : String
-- </vc-definitions>

-- <vc-theorems>
theorem string_merge_valid (s1 s2 : String) (c : Char)
  (h1 : s1.length > 0)
  (h2 : s2.length > 0) 
  (h3 : s1.contains c = true)
  (h4 : s2.contains c = true)
  (i1 : Nat) (i2 : Nat)
  (hi1 : findIndex s1 c = some i1)
  (hi2 : findIndex s2 c = some i2) :
  (string_merge s1 s2 c).take i1 = s1.take i1 ∧ 
  (string_merge s1 s2 c).drop i1 = s2.drop i2 ∧
  (string_merge s1 s2 c).length = i1 + s2.length - i2 := sorry

theorem string_merge_invalid (s1 s2 : String) (c : Char)
  (h1 : s1.length > 0)
  (h2 : s2.length > 0)
  (h3 : ¬s1.contains c ∨ ¬s2.contains c) :
  ∃ (err : StringMergeError), string_merge s1 s2 c = err.msg := sorry
-- </vc-theorems>