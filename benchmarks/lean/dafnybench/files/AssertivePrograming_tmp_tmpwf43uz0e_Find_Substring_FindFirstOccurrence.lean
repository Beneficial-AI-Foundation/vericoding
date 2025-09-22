-- <vc-preamble>
def ExistsSubstring (str1 str2 : String) : Prop :=
∃ offset : Nat, offset ≤ str1.length ∧
(∃ sub : String, sub = str1.extract ⟨offset⟩ ⟨str1.length⟩ ∧ str2.isPrefixOf sub)
def Post (str1 str2 : String) (found : Bool) (i : Nat) : Prop :=
(found ↔ ExistsSubstring str1 str2) ∧
(found → i + str2.length ≤ str1.length ∧
(∃ sub : String, sub = str1.extract ⟨i⟩ ⟨str1.length⟩ ∧ str2.isPrefixOf sub))
def Outter_Inv_correctness (str1 str2 : String) (found : Bool) (i : Nat) : Prop :=
(found → (i + str2.length ≤ str1.length ∧
(∃ sub : String, sub = str1.extract ⟨i⟩ ⟨str1.length⟩ ∧ str2.isPrefixOf sub))) ∧
(¬found ∧ 0 < i ∧ i ≤ str1.length ∧ i ≠ str2.length - 1 →
¬(ExistsSubstring (str1.extract 0 ⟨i⟩) str2)) ∧
(¬found → i ≤ str1.length)
def Inner_Inv_correctness (str1 str2 : String) (i : Nat) (j : Int) (found : Bool) : Prop :=
0 ≤ j ∧ j ≤ i ∧
j < str2.length ∧
i < str1.length ∧
((str1.get ⟨i⟩ = str2.get ⟨j.toNat⟩) →
(∃ sub : String, sub = str1.extract ⟨i⟩ ⟨str1.length⟩ ∧
(∃ sub2 : String, sub2 = str2.extract ⟨j.toNat⟩ ⟨str2.length⟩ ∧ sub2.isPrefixOf sub))) ∧
(found → j = 0 ∧ str1.get ⟨i⟩ = str2.get ⟨j.toNat⟩)
def Inner_Inv_Termination (str1 str2 : String) (i : Nat) (j : Int)
(old_i old_j : Nat) : Prop :=
old_j - j = old_i - i
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindFirstOccurrence (str1 str2 : String) : (Bool × Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindFirstOccurrence_spec (str1 str2 : String) :
let (found, i) := FindFirstOccurrence str1 str2
Post str1 str2 found i :=
sorry
-- </vc-theorems>