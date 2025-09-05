`late_clock` function receive an array with 4 digits and should return the latest time that can be built with those digits.
The time should be in `HH:MM` format.

Examples:
```
[1, 9, 8, 3] => 19:38
[9, 1, 2, 5] => 21:59
```

You can suppose the input is correct and you can build from it a correct 24-hour time.

def isValidTime (t : Time) : Prop := 
  t.hours ≤ 23 ∧ t.minutes ≤ 59

def lateClock (digits : List Nat) : String :=
sorry

def toNat (c : Char) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded