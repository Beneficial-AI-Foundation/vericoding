import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def toMultiset (s : String) : Array Char :=
s.data.toArray

def msetEqual (s t : Array Char) : Bool :=
decide (s = t)

def isAnagram (s t : String) : Bool :=
msetEqual (toMultiset s) (toMultiset t)
-- </vc-definitions>

-- <vc-theorems>
theorem toMultiset_spec (s : String) :
toMultiset s = s.data.toArray :=
by rfl

theorem msetEqual_spec (s t : Array Char) :
msetEqual s t = (s = t) :=
by simp [msetEqual]

theorem isAnagram_spec (s t : String) :
isAnagram s t = (s.data.toArray = t.data.toArray) :=
by simp [isAnagram, msetEqual, toMultiset]
-- </vc-theorems>
