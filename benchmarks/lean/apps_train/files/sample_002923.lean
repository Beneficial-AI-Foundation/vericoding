In this Kata, you will be given directions and your task will be to find your way back. 
```Perl
solve(["Begin on Road A","Right on Road B","Right on Road C","Left on Road D"]) = ['Begin on Road D', 'Right on Road C', 'Left on Road B', 'Left on Road A']
solve(['Begin on Lua Pkwy', 'Right on Sixth Alley', 'Right on 1st Cr']) =  ['Begin on 1st Cr', 'Left on Sixth Alley', 'Left on Lua Pkwy']
```

More examples in test cases. 

Good luck!

Please also try [Simple remove duplicates](https://www.codewars.com/kata/5ba38ba180824a86850000f7)

def solve : List String → List String := sorry

def extractDirections (commands : List String) : List Direction := sorry

def extractRoads (commands : List String) : List String := sorry

def isLeftOrRight (d : Direction) : Bool :=
  match d with
  | Direction.Left => true
  | Direction.Right => true
  | _ => false

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
