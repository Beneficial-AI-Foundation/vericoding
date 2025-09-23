-- <vc-preamble>
def isPrefixPred (pre str : String) : Prop :=
(pre.length ≤ str.length) ∧
(pre = str.take pre.length)

def isNotPrefixPred (pre str : String) : Prop :=
(pre.length > str.length) ∨
(pre ≠ str.take pre.length)

def isSubstringPred (sub str : String) : Prop :=
∃ i, 0 ≤ i ∧ i ≤ str.length ∧ isPrefixPred sub (str.drop i)

def isNotSubstringPred (sub str : String) : Prop :=
∀ i, 0 ≤ i ∧ i ≤ str.length → isNotPrefixPred sub (str.drop i)

def haveCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∃ i1 j1, 0 ≤ i1 ∧ i1 ≤ str1.length - k ∧ j1 = i1 + k ∧
isSubstringPred (str1.extract ⟨i1⟩ ⟨j1-i1⟩) str2

def haveNotCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∀ i1 j1, 0 ≤ i1 ∧ i1 ≤ str1.length - k ∧ j1 = i1 + k →
isNotSubstringPred (str1.extract ⟨i1⟩ ⟨j1-i1⟩) str2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrefix (pre str : String) : Bool :=
sorry

def isSubstring (sub str : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isPrefix_spec (pre str : String) :
(¬isPrefix pre str ↔ isNotPrefixPred pre str) ∧
(isPrefix pre str ↔ isPrefixPred pre str) :=
sorry

theorem isSubstring_spec (sub str : String) :
isSubstring sub str ↔ isSubstringPred sub str :=
sorry
-- </vc-theorems>