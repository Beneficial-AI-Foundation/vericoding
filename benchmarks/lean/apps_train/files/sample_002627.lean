/-
How many licks does it take to get to the tootsie roll center of a tootsie pop?

A group of engineering students from Purdue University reported that its licking machine, modeled after a human tongue, took an average of 364 licks to get to the center of a Tootsie Pop. Twenty of the group's volunteers assumed the licking challenge-unassisted by machinery-and averaged 252 licks each to the center.

Your task, if you choose to accept it, is to write a function that will return the number of licks it took to get to the tootsie roll center of a tootsie pop, given some environmental variables.

Everyone knows it's harder to lick a tootsie pop in cold weather but it's easier if the sun is out. You will be given an object of environmental conditions for each trial paired with a value that will increase or decrease the number of licks. The environmental conditions all apply to the same trial.

Assuming that it would normally take 252 licks to get to the tootsie roll center of a tootsie pop, return the new total of licks along with the condition that proved to be most challenging (causing the most added licks) in that trial.

Example:
```
totalLicks({ "freezing temps": 10, "clear skies": -2 });
```
Should return:
```
"It took 260 licks to get to the tootsie roll center of a tootsie pop. The toughest challenge was freezing temps."
```
Other cases:
If there are no challenges, the toughest challenge sentence should be omitted. If there are multiple challenges with the highest toughest amount, the first one presented will be the toughest.
If an environment variable is present, it will be either a positive or negative integer. No need to validate.

Check out my other 80's Kids Katas:

80's Kids #1: How Many Licks Does It Take
80's Kids #2: Help Alf Find His Spaceship
80's Kids #3: Punky Brewster's Socks
80's Kids #4: Legends of the Hidden Temple
80's Kids #5: You Can't Do That on Television
80's Kids #6: Rock 'Em, Sock 'Em Robots
80's Kids #7: She's a Small Wonder
80's Kids #8: The Secret World of Alex Mack
80's Kids #9: Down in Fraggle Rock 
80's Kids #10: Captain Planet
-/

def String.containsSubstr (s : String) (sub : String) : Bool := sorry

def List.sum (xs : List Int) : Int := 
  match xs with
  | [] => 0
  | x :: rest => x + rest.sum

structure Environment where
  modifiers : List (String × Int)

-- <vc-helpers>
-- </vc-helpers>

def total_licks (env : Environment) : String := sorry

theorem total_licks_base_text (env : Environment) :
  let result := total_licks env
  (result.startsWith "It took") ∧ 
  (result.containsSubstr " licks to get to the tootsie roll center of a tootsie pop") :=
sorry

theorem total_licks_contains_sum (env : Environment) :
  let expected := 252 + (env.modifiers.map Prod.snd).sum
  let result := total_licks env
  result.containsSubstr (toString expected) :=
sorry

theorem total_licks_toughest_challenge (env : Environment) :
  let maxVal := (env.modifiers.map Prod.snd).maximum?.getD 0
  let result := total_licks env
  if maxVal > 0 then
    (result.containsSubstr "The toughest challenge was") ∧
    (env.modifiers.find? (fun p => p.2 = maxVal)).map (fun p => result.containsSubstr p.1) = some true
  else
    ¬(result.containsSubstr "The toughest challenge was") :=
sorry

theorem total_licks_no_positive_challenges 
  (env : Environment)
  (h : ∀ p ∈ env.modifiers, p.2 ≤ 0) :
  ¬((total_licks env).containsSubstr "The toughest challenge was") :=
sorry

theorem total_licks_always_has_toughest_challenge
  (env : Environment)
  (h1 : env.modifiers.length > 0)
  (h2 : ∀ p ∈ env.modifiers, p.2 > 0) :
  (total_licks env).containsSubstr "The toughest challenge was" :=
sorry

/-
info: 'It took 260 licks to get to the tootsie roll center of a tootsie pop. The toughest challenge was freezing temps.'
-/
-- #guard_msgs in
-- #eval total_licks {"freezing temps": 10, "clear skies": -2}

/-
info: 'It took 245 licks to get to the tootsie roll center of a tootsie pop.'
-/
-- #guard_msgs in
-- #eval total_licks {"happiness": -5, "clear skies": -2}

/-
info: 'It took 512 licks to get to the tootsie roll center of a tootsie pop. The toughest challenge was evil wizards.'
-/
-- #guard_msgs in
-- #eval total_licks {"dragons": 100, "evil wizards": 110, "trolls": 50}

-- Apps difficulty: introductory
-- Assurance level: unguarded