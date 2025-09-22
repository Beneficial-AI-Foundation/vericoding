-- <vc-preamble>
def isSubstring (sub : Array Char) (str : Array Char) : Prop :=
∃ i, 0 ≤ i ∧ i ≤ str.size - sub.size ∧
(∀ j, 0 ≤ j ∧ j < sub.size → str[i + j]! = sub[j]!)

def isPrefixPred (pre str : String) : Prop :=
pre.length ≤ str.length ∧
(∀ i, 0 ≤ i ∧ i < pre.length → pre.get ⟨i⟩ = str.get ⟨i⟩)

def isNotPrefixPred (pre str : String) : Prop :=
pre.length > str.length ∨
(∃ i, 0 ≤ i ∧ i < pre.length ∧ pre.get ⟨i⟩ ≠ str.get ⟨i⟩)

def isSubstringPred (sub str : String) : Prop :=
∃ i, 0 ≤ i ∧ i ≤ str.length ∧ isPrefixPred sub (str.drop i)

def isNotSubstringPred (sub str : String) : Prop :=
∀ i, 0 ≤ i ∧ i ≤ str.length → isNotPrefixPred sub (str.drop i)

def haveCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∃ i1, 0 ≤ i1 ∧ i1 ≤ str1.length - k ∧
isSubstringPred (str1.extract ⟨i1⟩ ⟨k⟩) str2

def haveNotCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∀ i1, 0 ≤ i1 ∧ i1 ≤ str1.length - k →
isNotSubstringPred (str1.extract ⟨i1⟩ ⟨k⟩) str2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def haveCommonKSubstring (k : Nat) (str1 str2 : String) : Bool :=
sorry

def maxCommonSubstringLength (str1 str2 : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem haveCommonKSubstring_spec (k : Nat) (str1 str2 : String) :
haveCommonKSubstring k str1 str2 = true ↔ haveCommonKSubstringPred k str1 str2 :=
sorry

theorem maxCommonSubstringLength_spec (str1 str2 : String) :
str1.length ≤ str2.length →
(∀ k, maxCommonSubstringLength str1 str2 < k ∧ k ≤ str1.length →
¬haveCommonKSubstringPred k str1 str2) ∧
haveCommonKSubstringPred (maxCommonSubstringLength str1 str2) str1 str2 :=
sorry
-- </vc-theorems>