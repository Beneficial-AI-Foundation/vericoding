-- <vc-preamble>
def ValidEvent : Type := String

def VALID_EVENTS : List ValidEvent := 
  ["cw", "CW", "cat", "CAT", "dog", "DOG", "movie", "MOVIE"]

def isValidEvent (event : String) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def howMuchCoffee (events : List String) : Nat ⊕ String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_events_ignored (events : List String) : 
  (∀ e ∈ events, e ∉ VALID_EVENTS) → 
  howMuchCoffee events = .inl 0 :=
sorry

theorem valid_events (events : List String) :
  (∀ e ∈ events, e ∈ VALID_EVENTS) →
  let total := events.foldl (fun acc e => acc + if e.all Char.isUpper then 2 else 1) 0
  if total > 3 
  then howMuchCoffee events = .inr "You need extra sleep"
  else howMuchCoffee events = .inl total :=
sorry

theorem single_event_empty :
  howMuchCoffee [] = .inl 0 :=
sorry

theorem single_valid_event (event : String) :
  event ∈ VALID_EVENTS →
  howMuchCoffee [event] = .inl (if event.all Char.isUpper then 2 else 1) :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval how_much_coffee []

/-
info: 1
-/
-- #guard_msgs in
-- #eval how_much_coffee ["cw"]

/-
info: 2
-/
-- #guard_msgs in
-- #eval how_much_coffee ["CW"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval how_much_coffee ["cw", "CAT"]

/-
info: 'You need extra sleep'
-/
-- #guard_msgs in
-- #eval how_much_coffee ["cw", "CAT", "DOG"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval how_much_coffee ["cw", "CAT", "cw=others"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded