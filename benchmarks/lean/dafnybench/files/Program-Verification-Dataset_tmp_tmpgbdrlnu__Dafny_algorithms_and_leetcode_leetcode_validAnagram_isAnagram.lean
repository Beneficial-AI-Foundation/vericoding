-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toMultiset (s : String) : Array Char :=
sorry

def msetEqual (s t : Array Char) : Bool :=
sorry

def isAnagram (s t : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem toMultiset_spec (s : String) :
toMultiset s = s.data.toArray :=
sorry

theorem msetEqual_spec (s t : Array Char) :
msetEqual s t = (s = t) :=
sorry

theorem isAnagram_spec (s t : String) :
isAnagram s t = (s.data.toArray = t.data.toArray) :=
sorry
-- </vc-theorems>