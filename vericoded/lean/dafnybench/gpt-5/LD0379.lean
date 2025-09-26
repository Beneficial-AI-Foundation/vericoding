import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem propext_of_iff {P Q : Prop} (h : P ↔ Q) : P = Q := propext h
-- </vc-helpers>

-- <vc-definitions>
def toMultiset (s : String) : Array Char :=
s.data.toArray

def msetEqual (s t : Array Char) : Bool :=
if s = t then true else false

def isAnagram (s t : String) : Bool :=
if s.data.toArray = t.data.toArray then true else false
-- </vc-definitions>

-- <vc-theorems>
theorem toMultiset_spec (s : String) :
toMultiset s = s.data.toArray :=
rfl

theorem msetEqual_spec (s t : Array Char) :
msetEqual s t = (s = t) :=
by
  apply propext
  by_cases h : s = t
  · simp [msetEqual, h]
  · simp [msetEqual, h]

theorem isAnagram_spec (s t : String) :
isAnagram s t = (s.data.toArray = t.data.toArray) :=
by
  apply propext
  by_cases h : s.data.toArray = t.data.toArray
  · simp [isAnagram, h]
  · simp [isAnagram, h]
-- </vc-theorems>
