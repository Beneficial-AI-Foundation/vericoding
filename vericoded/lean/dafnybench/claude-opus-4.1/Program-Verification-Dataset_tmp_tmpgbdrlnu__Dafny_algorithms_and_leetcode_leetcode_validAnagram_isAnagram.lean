import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def toMultiset (s : String) : Array Char :=
s.data.toArray

def msetEqual (s t : Array Char) : Bool :=
s == t

def isAnagram (s t : String) : Bool :=
s.data.toArray == t.data.toArray
-- </vc-definitions>

-- <vc-theorems>
theorem toMultiset_spec (s : String) :
toMultiset s = s.data.toArray :=
rfl

theorem msetEqual_spec (s t : Array Char) :
msetEqual s t = (s = t) :=
by simp [msetEqual]

theorem isAnagram_spec (s t : String) :
isAnagram s t = (s.data.toArray = t.data.toArray) :=
by simp [isAnagram]
-- </vc-theorems>
