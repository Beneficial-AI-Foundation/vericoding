In this Kata, you will be given an array of numbers in which two numbers occur once and the rest occur only twice. Your task will be to return the sum of the numbers that occur only once. 

For example, `repeats([4,5,7,5,4,8]) = 15` because only the numbers `7` and `8` occur once, and their sum is `15`.

More examples in the test cases. 

```if:csharp
Documentation:
Kata.Repeats Method (List<Int32>)

Takes a list where all ints are repeated twice, except two ints, and returns the sum of the ints of a list where those ints only occur once.

Syntax

public
static
int Repeats(
List<int> source
    )

Parameters

source

Type: System.Collections.Generic.List<Int32>
The list to process.

Return Value

Type: System.Int32
  The sum of the elements of the list where those elements have no duplicates.

```

Good luck!

If you like this Kata, please try: 

[Sum of prime-indexed elements](https://www.codewars.com/kata/59f38b033640ce9fc700015b)

[Sum of integer combinations](https://www.codewars.com/kata/59f3178e3640cef6d90000d5)

def repeats (arr : List Int) : Int := sorry

def sumList : List Int → Int
  | [] => 0
  | (h::t) => h + sumList t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
