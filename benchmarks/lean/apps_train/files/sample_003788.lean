Two Joggers
===

Description
---
Bob and Charles are meeting for their weekly jogging tour. They both start at the same spot called "Start" and they each run a different lap, which may (or may not) vary in length. Since they know each other for a long time already, they both run at the exact same speed.

Illustration
---
Example where Charles (dashed line) runs a shorter lap than Bob:

![Example laps](http://www.haan.lu/files/7713/8338/6140/jogging.png "Example laps")

Task
---
Your job is to complete the function **nbrOfLaps(x, y)** that, given the length of the laps for Bob and Charles, finds the number of laps that each jogger has to complete before they meet each other again, at the same time, at the start.

The function takes two arguments:

1. The length of Bob's lap (larger than 0)
2. The length of Charles' lap (larger than 0)  

The function should return an array (`Tuple` in C#) containing exactly two numbers:

1. The first number is the number of laps that Bob has to run
2. The second number is the number of laps that Charles has to run

Examples:
```python
nbr_of_laps(5, 3) # returns (3, 5)
nbr_of_laps(4, 6) # returns (3, 2)
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible