

/-!
{
"name": "Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_normal_data_completion_MaxPerdV2_max",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_normal_data_completion_MaxPerdV2_max",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Contains checks if value v exists in array a up to index n -/
def contains (v : Int) (a : Array Int) (n : Nat) : Prop :=
∃ j, 0 ≤ j ∧ j < n ∧ a[j]! = v

/-- Upper bound checks if v is greater than or equal to all elements in array a up to index n -/
def upper_bound (v : Int) (a : Array Int) (n : Nat) : Prop :=
∀ j, 0 ≤ j ∧ j < n → a[j]! ≤ v

/-- Is max checks if m is both contained in array a and is an upper bound for all elements up to n -/
def is_max (m : Int) (a : Array Int) (n : Nat) : Prop :=
contains m a n ∧ upper_bound m a n

/-- Max function specification -/
def max (a : Array Int) (n : Nat) : Int :=
sorry

/-- Max function specification theorem -/
theorem max_spec (a : Array Int) (n : Nat) :
0 < n ∧ n ≤ a.size →
is_max (max a n) a n := sorry
