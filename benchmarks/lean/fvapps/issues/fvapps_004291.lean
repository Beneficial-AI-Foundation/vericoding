-- <vc-preamble>
def day_plan (hours tasks duration : Int) : List Int ⊕ String := sorry

def List.get_even_indices (l : List Int) : List Int := 
  l.enum.filter (fun p => p.fst % 2 = 0) |>.map (fun p => p.snd)

def List.get_odd_indices (l : List Int) : List Int :=
  l.enum.filter (fun p => p.fst % 2 = 1) |>.map (fun p => p.snd)

def List.allDistinctEq (l : List Int) : Bool :=
  match l with
  | [] => true
  | x::xs => xs.all (fun y => y = x)

def validDurationDistribution (schedule : List Int) (duration : Int) (tasks : Nat) : Prop :=
  schedule.get? 0 = some duration ∧ 
  schedule.get_even_indices = List.replicate tasks duration

def validBreakDistribution (schedule : List Int) : Prop := 
  let breaks := schedule.get_odd_indices
  breaks.all (· ≥ 0) ∧ breaks.allDistinctEq
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validTotalDuration (schedule : List Int) (hours : Int) : Prop :=
  schedule.foldl (· + ·) 0 ≤ hours * 60
-- </vc-definitions>

-- <vc-theorems>
theorem day_plan_properties {hours tasks duration : Int} 
  (h_hours : hours ≥ 4 ∧ hours ≤ 24)
  (h_tasks : tasks ≥ 1 ∧ tasks ≤ 8)  
  (h_duration : duration ≥ 5 ∧ duration ≤ 60) :
  let result := day_plan hours tasks duration
  if tasks * duration > hours * 60 then
    result = Sum.inr "You're not sleeping tonight!"
  else
    (∃ schedule : List Int,
      result = Sum.inl schedule ∧
      schedule.length = 2 * tasks - 1 ∧
      validDurationDistribution schedule duration tasks.toNat ∧
      validBreakDistribution schedule ∧
      validTotalDuration schedule hours) := 
sorry

/-
info: [30, 82, 30, 82, 30, 82, 30, 82, 30]
-/
-- #guard_msgs in
-- #eval day_plan 8 5 30

/-
info: "You're not sleeping tonight!"
-/
-- #guard_msgs in
-- #eval day_plan 3 5 60

/-
info: [60]
-/
-- #guard_msgs in
-- #eval day_plan 2 1 60
-- </vc-theorems>