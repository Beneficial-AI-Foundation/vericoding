Algorithmic predicament - Bug Fixing #9

Oh no! Timmy's algorithim has gone wrong! help Timmy fix his algorithim! 

Task
Your task is to fix timmy's algorithim so it returns the group name with the highest total age. 

You will receive two groups of `people` objects, with two properties `name` and `age`. The name property is a string and the age property is a number.  
Your goal is to make the total the age of all people having the same name through both groups and return the name of the one with the highest age. If two names have the same total age return the first alphabetical name.

def highest_age (persons1 persons2 : List Person) : Option String := sorry

theorem highest_age_empty_lists : 
  highest_age [] [] = none := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded