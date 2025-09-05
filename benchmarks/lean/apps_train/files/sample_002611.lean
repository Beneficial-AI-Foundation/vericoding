Create a function that interprets code in the esoteric language **Poohbear**

## The Language

Poohbear is a stack-based language largely inspired by Brainfuck. It has a maximum integer value of 255, and 30,000 cells. The original intention of Poohbear was to be able to send messages that would, to most, be completely indecipherable: 
Poohbear Wiki

* For the purposes of this kata, you will make a version of Poohbear that has **infinite** memory cells in **both directions** (so you do not need to limit cells to 30,000)
* Cells have a default value of 0
* Each cell can hold one byte of data.  Once a cell's value goes above 255, it wraps around to 0.  If a cell's value goes below 0, it wraps to 255.
* If the result of an operation isn't an int, round the result down to the nearest one.
* Your interpreter should ignore any non-command characters in the code.
* If you come to a `W` in the code and the current cell is equal to 0, jump to the corresponding `E`.
* If you come to an `E` in the code and the current cell is **not** 0, jump back to the corresponding `W`.

Here are the Poohbear commands: 

| Command | Definition
|---| -------------------------
| + | Add 1 to the current cell
| - | Subtract 1 from the current cell
| > | Move the cell pointer 1 space to the right
| < | Move the cell pointer 1 space to the left
| c | "Copy" the current cell
| p | Paste the "copied" cell into the current cell
| W | While loop - While the current cell is not equal to 0
| E | Closing character for loops
| P | Output the current cell's value as ascii
| N | Output the current cell's value as an integer
| T | Multiply the current cell by 2
| Q | Square the current cell
| U | Square root the current cell's value
| L | Add 2 to the current cell
| I | Subtract 2 from the current cell
| V | Divide the current cell by 2
| A | Add the copied value to the current cell's value
| B | Subtract the copied value from the current cell's value
| Y | Multiply the current cell's value by the copied value
| D | Divide the current cell's value by the copied value.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded