Paul is an excellent coder and sits high on the CW leaderboard. He solves kata like a banshee but would also like to lead a normal life, with other activities. But he just can't stop solving all the kata!!

Given an array (x) you need to calculate the Paul Misery Score. The values are worth the following points:

kata = 5
Petes kata = 10
life = 0
eating = 1

The Misery Score is the total points gained from the array. Once you have the total, return as follows:

<40        = 'Super happy!'<70   >=40 = 'Happy!'<100  >=70 = 'Sad!'\>=100       = 'Miserable!'

def points : Activity → Nat 
  | Activity.life => 0
  | Activity.eating => 1
  | Activity.kata => 5
  | Activity.petes_kata => 10

def sumList : List Nat → Nat  
  | [] => 0
  | h :: t => h + sumList t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
