-- <vc-preamble>
def isNotPrefixPred (pre str : String) : Prop :=
(pre.length > str.length) ∨
pre ≠ str.take pre.length

def isPrefixPredicate (pre str : String) : Prop :=
str.length ≥ pre.length ∧ pre ≤ str

def isSubstringPredicate (sub str : String) : Prop :=
str.length ≥ sub.length ∧
∃ i, 0 ≤ i ∧ i ≤ str.length ∧ isPrefixPredicate sub (str.drop i)

def haveCommonKSubstringPredicate (k : Nat) (str1 str2 : String) : Prop :=
str1.length ≥ k ∧ str2.length ≥ k ∧
∃ i, 0 ≤ i ∧ i ≤ str1.length - k ∧
isSubstringPredicate ((str1.drop i).take k) str2

def maxCommonSubstringPredicate (str1 str2 : String) (len : Nat) : Prop :=
∀ k, len < k ∧ k ≤ str1.length → ¬(haveCommonKSubstringPredicate k str1 str2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrefix (pre str : String) : Bool :=
sorry

def isSubstring (sub str : String) : Bool :=
sorry

def haveCommonKSubstring (k : Nat) (str1 str2 : String) : Bool :=
sorry

def maxCommonSubstringLength (str1 str2 : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isPrefix_spec (pre str : String) :
¬(isPrefix pre str) ↔ isNotPrefixPred pre str ∧
(isPrefix pre str ↔ isPrefixPredicate pre str) :=
sorry

theorem isSubstring_spec (sub str : String) :
isSubstring sub str ↔ isSubstringPredicate sub str :=
sorry

theorem haveCommonKSubstring_spec (k : Nat) (str1 str2 : String) :
(str1.length < k ∨ str2.length < k → ¬(haveCommonKSubstring k str1 str2)) ∧
(haveCommonKSubstringPredicate k str1 str2 ↔ haveCommonKSubstring k str1 str2) :=
sorry

theorem maxCommonSubstringLength_spec (str1 str2 : String) :
let len := maxCommonSubstringLength str1 str2
len ≤ str1.length ∧ len ≤ str2.length ∧
len ≥ 0 ∧
maxCommonSubstringPredicate str1 str2 len :=
sorry
-- </vc-theorems>