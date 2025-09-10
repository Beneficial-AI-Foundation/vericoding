predicate ValidInput(input: string)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B)) &&
    result == IntToString(ContestStartTime(A, B)) + "\n"
}

// <vc-helpers>
predicate ValidInput(input: string)
{
    exists A, B :: (0 <= A <= 23 && 0 <= B <= 23 &&
        (input == IntToString(A) + " " + IntToString(B) + "\n" ||
         input == IntToString(A) + " " + IntToString(B)))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: (0 <= A <= 23 && 0 <= B <= 23 &&
        (input == IntToString(A) + " " + IntToString(B) + "\n" ||
         input == IntToString(A) + " " + IntToString(B)) &&
        result == IntToString(ContestStartTime(A, B)) + "\n")
}

function DigitToString(d: int): string
{
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
}

function IntToString(i: int): string
{
    if i < 0 then "-" + IntToString(-i)
    else if i < 10 then DigitToString(i)
    else DigitToString(i / 10) + DigitToString(i % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
  var A, B :| 0 <= A <= 23 && 0 <= B <= 23 &&
      (input == IntToString(A) + " " + IntToString(B) + "\n" ||
       input == IntToString(A) + " " + IntToString(B));
  result := IntToString(ContestStartTime(A, B)) + "\n";
}
// </vc-code>

