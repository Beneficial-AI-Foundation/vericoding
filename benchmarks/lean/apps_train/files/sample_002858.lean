Reducing Problems - Bug Fixing #8

Oh no! Timmy's reduce is causing problems, Timmy's goal is to calculate the two teams scores and return the winner but timmy has gotten confused and sometimes teams don't enter their scores, total the scores out of 3! Help timmy fix his program!

Return true if team 1 wins or false if team 2 wins!

def List.sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + List.sum t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
