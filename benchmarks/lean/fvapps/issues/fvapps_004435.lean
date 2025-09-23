-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def createReport (names : List String) : List (String ⊕ Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem report_structure {names : List String} 
  (h : createReport names ≠ [Sum.inl "Disqualified data"]) :
  let result := createReport names;
  -- Result is a list
  (List.length result % 2 = 0)  
  -- Every even index is String, odd index is Nat > 0
  ∧ (∀ i, i < List.length result → 
      i % 2 = 0 → (∃ s : String, result.get! i = Sum.inl s)
      ∧ i % 2 = 1 → (∃ n : Nat, result.get! i = Sum.inr n ∧ n > 0)) :=
sorry

theorem sorted_codes {names : List String} 
  (h : createReport names ≠ [Sum.inl "Disqualified data"]) :
  let strings := List.filterMap (fun x => match x with 
    | Sum.inl s => some s
    | _ => none) (createReport names);
  List.Pairwise (fun x y => x ≤ y) strings :=
sorry

theorem labrador_disqualification {names : List String} 
  (h : ∃ entry ∈ names, entry = "Labrador Duck 1") :
  createReport names = [Sum.inl "Disqualified data"] :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval create_report ["Redhead 3", "Gadwall 1", "Smew 4", "Greater Scaup 10", "Redhead 3", "Gadwall 9", "Greater Scaup 15", "Common Eider 6"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval create_report ["Redhead 5", "Labrador Duck 9", "Blue-Winged Teal 25"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval create_report ["Canvasback 10", "Mallard 150", "American Wigeon 45"]
-- </vc-theorems>