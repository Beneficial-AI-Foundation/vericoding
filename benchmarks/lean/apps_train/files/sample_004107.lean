*This kata is based on [Project Euler Problem #349](https://projecteuler.net/problem=349). You may want to start with solving [this kata](https://www.codewars.com/kata/langtons-ant) first.*

---

[Langton's ant](https://en.wikipedia.org/wiki/Langton%27s_ant) moves on a regular grid of squares that are coloured either black or white.
The ant is always oriented in one of the cardinal directions (left, right, up or down) and moves  according to the following rules:
- if it is on a black square, it flips the colour of the square to white, rotates 90 degrees counterclockwise and moves forward one square.
- if it is on a white square, it flips the colour of the square to black, rotates 90 degrees clockwise and moves forward one square.

Starting with a grid that is **entirely white**, how many squares are black after `n` moves of the ant?

**Note:** `n` will go as high as 10^(20)

---

## My other katas

If you enjoyed this kata then please try [my other katas](https://www.codewars.com/collections/katas-created-by-anter69)! :-)

#### *Translations are welcome!*

def langtons_ant (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
