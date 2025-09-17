

/-!
{
"name": "Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings3_maxCommonSubstringLength",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings3_maxCommonSubstringLength",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate checking if sub is a substring of str -/
def isSubstring (sub str : String) : Prop :=
∃ i, 0 ≤ i ∧ i ≤ str.length - sub.length ∧ str.extract ⟨i⟩ ⟨i + sub.length⟩ = sub

/-- Predicate checking if pre is a prefix of str -/
def isPrefixPred (pre str : String) : Prop :=
pre.length ≤ str.length ∧ pre = str.take pre.length

/-- Predicate checking if pre is not a prefix of str -/
def isNotPrefixPred (pre str : String) : Prop :=
pre.length > str.length ∨ pre ≠ str.take pre.length

/-- Predicate checking if sub is a substring of str using prefix predicate -/
def isSubstringPred (sub str : String) : Prop :=
∃ i, 0 ≤ i ∧ i ≤ str.length ∧ isPrefixPred sub (str.drop i)

/-- Predicate checking if sub is not a substring of str using prefix predicate -/
def isNotSubstringPred (sub str : String) : Prop :=
∀ i, 0 ≤ i ∧ i ≤ str.length → isNotPrefixPred sub (str.drop i)

/-- Predicate checking if strings have a common substring of length k -/
def haveCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∃ i1 j1, 0 ≤ i1 ∧ i1 ≤ str1.length - k ∧ j1 = i1 + k ∧
isSubstringPred (str1.extract ⟨i1⟩ ⟨j1⟩) str2

/-- Predicate checking if strings do not have a common substring of length k -/
def haveNotCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∀ i1 j1, 0 ≤ i1 ∧ i1 ≤ str1.length - k ∧ j1 = i1 + k →
isNotSubstringPred (str1.extract ⟨i1⟩ ⟨j1⟩) str2

/-- Function checking if strings have a common substring of length k -/
def haveCommonKSubstring (k : Nat) (str1 str2 : String) : Bool := sorry

/-- Specification for haveCommonKSubstring -/
theorem haveCommonKSubstring_spec (k : Nat) (str1 str2 : String) :
haveCommonKSubstring k str1 str2 = true ↔ haveCommonKSubstringPred k str1 str2 := sorry

/-- Function finding the maximum length of common substring -/
def maxCommonSubstringLength (str1 str2 : String) : Nat := sorry

/-- Specification for maxCommonSubstringLength -/
theorem maxCommonSubstringLength_spec (str1 str2 : String) :
str1.length ≤ str2.length →
(∀ k, maxCommonSubstringLength str1 str2 < k ∧ k ≤ str1.length →
¬haveCommonKSubstringPred k str1 str2) ∧
haveCommonKSubstringPred (maxCommonSubstringLength str1 str2) str1 str2 := sorry
