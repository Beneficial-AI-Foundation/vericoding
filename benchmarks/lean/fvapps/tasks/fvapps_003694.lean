-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_honor_path (honor : Int) (target : Int) : Option (Int × Int) := sorry

theorem honor_path_empty_when_target_not_greater {honor target : Int} :
  target ≤ honor → get_honor_path honor target = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem honor_path_reaches_target {honor target : Int} (h: target > honor) : 
  match get_honor_path honor target with
  | none => False 
  | some (kyus1, kyus2) => honor + (kyus1 * 2 + kyus2) = target
  := sorry

theorem honor_path_optimal {honor target : Int} (h: target > honor) :
  match get_honor_path honor target with
  | none => False
  | some (kyus1, kyus2) => kyus2 ≤ 1 ∧ kyus1 ≥ 0
  := sorry
-- </vc-theorems>