Working from left-to-right if no digit is exceeded by the digit to its left it is called an increasing number; for example, 134468.

Similarly if no digit is exceeded by the digit to its right it is called a decreasing number; for example, 66420.

We shall call a positive integer that is neither increasing nor decreasing a "bouncy" number; for example, 155349.

Clearly there cannot be any bouncy numbers below one-hundred, but just over half of the numbers below one-thousand (525) are bouncy. In fact, the least number for which the proportion of bouncy numbers first reaches 50% is 538.

Surprisingly, bouncy numbers become more and more common and by the time we reach 21780 the proportion of bouncy numbers is equal to 90%.

#### Your Task

Complete the bouncyRatio function.

The input will be the target ratio.

The output should be the smallest number such that the proportion of bouncy numbers reaches the target ratio.

You should throw an Error for a ratio less than 0% or greater than 99%.

**Source**

  - https://projecteuler.net/problem=112

**Updates**

  - 26/10/2015: Added a higher precision test case.

def isDigit (c : Char) : Bool := sorry

def isBouncyStr (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
