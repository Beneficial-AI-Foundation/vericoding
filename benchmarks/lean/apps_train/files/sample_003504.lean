Given a number `n`, make a down arrow shaped pattern.

For example, when `n = 5`, the output would be:

    123454321
     1234321
      12321
       121
        1

and for `n = 11`, it would be:

    123456789010987654321
     1234567890987654321
      12345678987654321
       123456787654321
        1234567654321
         12345654321
          123454321
           1234321
            12321
             121
              1

An important thing to note in the above example is that the numbers greater than 9 still stay single digit, like after 9 it would be 0 - 9 again instead of 10 - 19.

Note: There are spaces for the indentation on the left of each line and no spaces on the right.

Have fun!

def get_a_down_arrow_of (n : Nat) : String :=
sorry

def String.lines (s : String) : List String :=
sorry

def String.padLeft (n : Nat) (c : Char) (s : String) : String :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded