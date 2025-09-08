/-
# The learning game - Machine Learning #1
Growing up you would have learnt a lot of things like not to stand in fire, to drink food and eat water and not to jump off very tall things But Machines have it difficult they cannot learn for themselves we have to tell them what to do, why don't we give them a chance to learn it for themselves?

### Task
Your task is to finish the Machine object. What the machine object must do is learn from its mistakes! The Machine will be given a command and a number you will return a random action. After the command has returned you will be given a response (true/false) if the response is true then you have done good, if the response is false then the action was a bad one. You must program the machine to learn to apply an action to a given command using the reponse given. Note: It must take no more than 20 times to teach an action to a command also different commands can have the same action.

### Info
- In the preloaded section there is a constant called ```ACTIONS``` it is a function that returns the 5 possible actions.
- In Java, this a constant ```Actions.FUNCTIONS``` of type ```List>```. 
- In C++, the actions can be accessed by ```get_action(i)(unsigned int num)``` where i chooses the function (and therefore can range from 0 to 4) and num is its argument.
- In python ```ACTIONS()``` returns a list of lambdas.
- In Golang ```Actions()``` retruns a function slice ```[]func(int) int```
-/

def Machine.command (m : Machine) (cmd : String) (n : Int) : Int := sorry
def Machine.response (m : Machine) (b : Bool) : Machine := sorry

-- <vc-helpers>
-- </vc-helpers>

def Machine.actions : List (Int → Int) := sorry

-- First command matches first action

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

-- Apps difficulty: interview
-- Assurance level: guarded