

/-!
{
"name": "Formal-Verification-Project_tmp_tmp9gmwsmyp_strings3_isSubstring",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Formal-Verification-Project_tmp_tmp9gmwsmyp_strings3_isSubstring",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate defining when one string is a prefix of another -/
def isPrefixPred (pre str : String) : Prop :=
(pre.length ≤ str.length) ∧
(pre = str.take pre.length)

/-- Predicate defining when one string is not a prefix of another -/
def isNotPrefixPred (pre str : String) : Prop :=
(pre.length > str.length) ∨
(pre ≠ str.take pre.length)

/-- Method checking if one string is a prefix of another -/
def isPrefix (pre str : String) : Bool := sorry

/-- Specification for isPrefix method -/
theorem isPrefix_spec (pre str : String) :
(¬isPrefix pre str ↔ isNotPrefixPred pre str) ∧
(isPrefix pre str ↔ isPrefixPred pre str) := sorry

/-- Predicate defining when one string is a substring of another -/
def isSubstringPred (sub str : String) : Prop :=
∃ i, 0 ≤ i ∧ i ≤ str.length ∧ isPrefixPred sub (str.drop i)

/-- Predicate defining when one string is not a substring of another -/
def isNotSubstringPred (sub str : String) : Prop :=
∀ i, 0 ≤ i ∧ i ≤ str.length → isNotPrefixPred sub (str.drop i)

/-- Predicate defining when two strings have a common substring of length k -/
def haveCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∃ i1 j1, 0 ≤ i1 ∧ i1 ≤ str1.length - k ∧ j1 = i1 + k ∧
isSubstringPred (str1.extract ⟨i1⟩ ⟨j1-i1⟩) str2

/-- Predicate defining when two strings do not have a common substring of length k -/
def haveNotCommonKSubstringPred (k : Nat) (str1 str2 : String) : Prop :=
∀ i1 j1, 0 ≤ i1 ∧ i1 ≤ str1.length - k ∧ j1 = i1 + k →
isNotSubstringPred (str1.extract ⟨i1⟩ ⟨j1-i1⟩) str2

/-- Method checking if one string is a substring of another -/
def isSubstring (sub str : String) : Bool := sorry

/-- Specification for isSubstring method -/
theorem isSubstring_spec (sub str : String) :
isSubstring sub str ↔ isSubstringPred sub str := sorry
