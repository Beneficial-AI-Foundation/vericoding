Every now and then people in the office moves teams or departments. Depending what people are doing with their time they can become more or less boring. Time to assess the current team.

```if-not:java
You will be provided with an object(staff) containing the staff names as keys, and the department they work in as values.
```

```if:java
You will be provided with an array of `Person` objects with each instance containing the name and department for a staff member.
~~~java
public class Person {
  public final String name;        // name of the staff member
  public final String department;  // department they work in
}
~~~
```

Each department has a different boredom assessment score, as follows:

accounts = 1
finance = 2 
canteen = 10 
regulation = 3 
trading = 6 
change = 6
IS = 8
retail = 5 
cleaning = 4
pissing about = 25

Depending on the cumulative score of the team, return the appropriate sentiment:

<=80: 'kill me now'
< 100 & > 80: 'i can handle this'
100 or over: 'party time!!'

The Office I - Outed
The Office III - Broken Photocopier
The Office IV - Find a Meeting Room
The Office V - Find a Chair

def VALID_DEPTS := ["accounts", "finance", "canteen", "regulation", "trading", 
                    "change", "IS", "retail", "cleaning", "pissing about"]

def scores : List (String × Nat) := [
  ("accounts", 1), ("finance", 2), ("canteen", 10), ("regulation", 3),
  ("trading", 6), ("change", 6), ("IS", 8), ("retail", 5),
  ("cleaning", 4), ("pissing about", 25)
]

def getScore (dept : String) : Nat :=
  match scores.find? (fun p => p.1 = dept) with
  | some p => p.2
  | none => 0

def getTotalScore (staff : List (String × String)) : Nat :=
  staff.foldl (fun acc x => acc + getScore x.2) 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded