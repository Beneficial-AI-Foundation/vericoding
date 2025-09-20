-- <vc-preamble>
def VALID_DEPTS := ["accounts", "finance", "canteen", "regulation", "trading", 
                    "change", "IS", "retail", "cleaning", "pissing about"]

def scores : List (String × Nat) := [
  ("accounts", 1), ("finance", 2), ("canteen", 10), ("regulation", 3),
  ("trading", 6), ("change", 6), ("IS", 8), ("retail", 5),
  ("cleaning", 4), ("pissing about", 25)
]

def getScore (dept : String) : Nat :=
  match scores.find? (fun p => p.1 = dept) with
  | some p => p.2
  | none => 0

def getTotalScore (staff : List (String × String)) : Nat :=
  staff.foldl (fun acc x => acc + getScore x.2) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def boredom (staff : List (String × String)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem boredom_output_valid (staff : List (String × String)) :
  let result := boredom staff
  result = "kill me now" ∨ result = "i can handle this" ∨ result = "party time!!" := 
  sorry

theorem boredom_threshold_low (staff : List (String × String)) 
  (h : ∀ x ∈ staff, x.2 ∈ VALID_DEPTS) :
  let total := getTotalScore staff
  total ≤ 80 → boredom staff = "kill me now" :=
  sorry

theorem boredom_threshold_mid (staff : List (String × String))
  (h : ∀ x ∈ staff, x.2 ∈ VALID_DEPTS) :
  let total := getTotalScore staff
  total > 80 ∧ total < 100 → boredom staff = "i can handle this" :=
  sorry

theorem boredom_threshold_high (staff : List (String × String))
  (h : ∀ x ∈ staff, x.2 ∈ VALID_DEPTS) :
  let total := getTotalScore staff
  total ≥ 100 → boredom staff = "party time!!" :=
  sorry
-- </vc-theorems>