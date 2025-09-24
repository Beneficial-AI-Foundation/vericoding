-- <vc-preamble>
def HashMap.toArray {α β : Type} : HashMap α β → Array (α × β) :=
  fun _ => #[]

def isAye : String → Bool
| "aye" => true
| _ => false
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cannons_ready (gunners : HashMap Gunner Response) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cannons_ready_all_conditions {gunners : HashMap Gunner Response} :
  cannons_ready gunners = if (gunners.toArray.all (fun p => isAye p.2))
    then "Fire!"
    else "Shiver me timbers!"
  := sorry

theorem cannons_ready_all_aye {gunners : HashMap Gunner Response} :
  (gunners.toArray.all (fun p => isAye p.2)) →
  cannons_ready gunners = "Fire!"
  := sorry

theorem cannons_ready_all_nay {gunners : HashMap Gunner Response} :
  (gunners.toArray.all (fun p => ¬isAye p.2)) →
  cannons_ready gunners = "Shiver me timbers!"
  := sorry

/-
info: 'Shiver me timbers!'
-/
-- #guard_msgs in
-- #eval cannons_ready {"Joe": "nay", "Johnson": "nay", "Peter": "aye"}

/-
info: 'Fire!'
-/
-- #guard_msgs in
-- #eval cannons_ready {"Mike": "aye", "Joe": "aye", "Johnson": "aye", "Peter": "aye"}

/-
info: 'Shiver me timbers!'
-/
-- #guard_msgs in
-- #eval cannons_ready {"Joe": "aye", "Steve": "nay"}
-- </vc-theorems>