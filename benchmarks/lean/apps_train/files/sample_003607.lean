# Task
 John is new to spreadsheets. He is well aware of rows and columns, but he is not comfortable with spreadsheets numbering system.
```
Spreadsheet             Row Column
A1                      R1C1
D5                       R5C4
AA48                    R48C27
BK12                   R12C63```
Since John has a lot of work to do both in row-column and spreadsheet systems, he needs a program that converts cell numbers from one system to another.

# Example

 For `s = "A1"`, the result should be `"R1C1"`.

 For `s = "R48C27"`, the result should be `"AA48"`.

- Input/Output

 - `[input]` string `s`

  The position (in spreadsheet or row-column numbering system).

  `Spreadsheet : A1 to CRXO65535`

  `Row-Column: R1C1 to R65535C65535`

 - `[output]` a string

  The position (in the opposite format; if input was in spreadsheet system, the output should be int row-column system, and vise versa).

def spreadsheet (s : String) : String := sorry

def is_valid_a1 (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded