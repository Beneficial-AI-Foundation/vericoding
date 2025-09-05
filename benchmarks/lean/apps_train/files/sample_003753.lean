Write a function which outputs the positions of matching bracket pairs. The output should be a dictionary with keys the positions of the open brackets '(' and values the corresponding positions of the closing brackets ')'.

For example: input = "(first)and(second)" should return {0:6, 10:17}

If brackets cannot be paired or if the order is invalid (e.g. ')(') return False. In this kata we care only about the positions of round brackets '()', other types of brackets should be ignored.

def Pos2Nat (p : String.Pos) : Nat := sorry
def Nat2Pos (n : Nat) : String.Pos := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
