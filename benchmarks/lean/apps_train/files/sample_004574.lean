Complete the function so that it returns the number of seconds that have elapsed between the start and end times given.  

##### Tips:
- The start/end times are given as Date (JS/CoffeeScript), DateTime (C#), Time (Nim), datetime(Python) and Time (Ruby) instances.  
- The start time will always be before the end time.

def DateTime := Nat -- simplified representation
def TimeDelta := Nat -- simplified representation

instance : Add DateTime where
  add := Nat.add

instance : HAdd DateTime TimeDelta DateTime where
  hAdd := Nat.add

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded