Raj was to move up through a pattern of stairs of a given number **(n)**. Help him to get to the    top using the function **stairs**.

##Keep in mind :
  * If **n<1** then return ' ' .
  * There are a lot of spaces before the stair starts except for **pattern(1)**

##Examples :
  pattern(1)

          1 1

  pattern(6)

                          1 1
                      1 2 2 1  
                  1 2 3 3 2 1
              1 2 3 4 4 3 2 1
          1 2 3 4 5 5 4 3 2 1
      1 2 3 4 5 6 6 5 4 3 2 1

pattern(12)

                                                  1 1
                                              1 2 2 1
                                          1 2 3 3 2 1
                                      1 2 3 4 4 3 2 1
                                  1 2 3 4 5 5 4 3 2 1
                              1 2 3 4 5 6 6 5 4 3 2 1
                          1 2 3 4 5 6 7 7 6 5 4 3 2 1
                      1 2 3 4 5 6 7 8 8 7 6 5 4 3 2 1
                  1 2 3 4 5 6 7 8 9 9 8 7 6 5 4 3 2 1
              1 2 3 4 5 6 7 8 9 0 0 9 8 7 6 5 4 3 2 1
          1 2 3 4 5 6 7 8 9 0 1 1 0 9 8 7 6 5 4 3 2 1
      1 2 3 4 5 6 7 8 9 0 1 2 2 1 0 9 8 7 6 5 4 3 2 1

def stairs (n : Int) : String := sorry 
def step (n : Int) : String := sorry

def splitLines (s : String) : List String := sorry
def rightJustify (s : String) (width : Int) : String := sorry

def isDigit (c : Char) : Bool := sorry
def listToString (l : List Nat) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded