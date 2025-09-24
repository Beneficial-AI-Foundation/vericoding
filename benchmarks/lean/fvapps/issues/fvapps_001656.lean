-- <vc-preamble>
def Machine.command (m : Machine) (cmd : String) (n : Int) : Int := sorry
def Machine.response (m : Machine) (b : Bool) : Machine := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Machine.actions : List (Int → Int) := sorry

-- First command matches first action
-- </vc-definitions>

-- <vc-theorems>
theorem initial_command_matches_first_action (cmd : String) (n : Int) :
  let m : Machine := default
  let firstAction := (Machine.actions.head! : Int → Int)
  Machine.command m cmd n = firstAction n := sorry

-- False response changes behavior eventually

theorem false_response_changes_behavior (cmd : String) (n : Int) 
  (h : 1 ≤ n ∧ n ≤ 100) :
  let m : Machine := default
  let first := Machine.command m cmd n
  ∃ i : Nat, i ≤ 3 ∧
    let m' := Machine.response m false
    let second := Machine.command m' cmd n
    second ≠ first := sorry

-- Cycles through multiple actions

theorem cycling_through_actions (cmd : String) (n : Int)
  (h : 1 ≤ n ∧ n ≤ 100) :
  let m : Machine := default
  let r1 := Machine.command m cmd n
  let m1 := Machine.response m false
  let r2 := Machine.command m1 cmd n
  let m2 := Machine.response m1 false
  let r3 := Machine.command m2 cmd n
  let results := [r1, r2, r3]
  (results.eraseDups).length ≥ 2 := sorry

-- Different commands are independent

theorem commands_independent (cmd1 cmd2 : String) (h : cmd1 ≠ cmd2) :
  let m : Machine := default
  let r1 := Machine.command m cmd1 1
  let m' := Machine.response m false
  let r2 := Machine.command m' cmd2 1
  let firstAction := (Machine.actions.head! : Int → Int)
  r2 = firstAction 1 := sorry

-- True response maintains same action

theorem true_response_maintains_action (cmd : String) (n : Int) :
  let m : Machine := default
  let first := Machine.command m cmd n
  let m' := Machine.response m true
  let second := Machine.command m' cmd n
  first = second := sorry
-- </vc-theorems>