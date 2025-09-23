-- <vc-preamble>
def get_price : Item → Float 
| Item.apple => 0.5
| Item.banana => 0.5  
| Item.orange => 0.7

def ring_up (items : List (Item × Nat)) (promos : List String := []) : Float :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum (l : List Float) : Float :=
  match l with
  | [] => 0
  | h :: t => h + list_sum t
-- </vc-definitions>

-- <vc-theorems>
theorem ring_up_nonnegative (items : List (Item × Nat)) (promos : List String) :
  ring_up items promos ≥ 0 :=
sorry

theorem ring_up_equals_sum_when_no_promos (items : List (Item × Nat)) :
  ring_up items [] = list_sum (items.map (fun (i,q) => get_price i * q.toFloat)) :=
sorry

theorem ring_up_empty_is_zero :
  ring_up [] [] = 0 :=
sorry

theorem ring_up_zero_quantities (items : List (Item × Nat)) (h: ∀ p ∈ items, p.2 = 0) :
  ring_up items [] = 0 :=
sorry

theorem ring_up_three_for_one_apple :
  ring_up [(Item.apple, 3)] ["3 for 1.00"] = 1.00 :=
sorry

theorem ring_up_bogo_banana :
  ring_up [(Item.banana, 2)] ["buy 1 get 1"] = 0.50 :=
sorry

/-
info: 0.8
-/
-- #guard_msgs in
-- #eval ring_up {"apple": 2}

/-
info: 1.0
-/
-- #guard_msgs in
-- #eval ring_up {"apple": 3} {"apple": "3 for 1.00"}

/-
info: 0.5
-/
-- #guard_msgs in
-- #eval ring_up {"banana": 2} {"banana": "buy 1 get 1"}
-- </vc-theorems>