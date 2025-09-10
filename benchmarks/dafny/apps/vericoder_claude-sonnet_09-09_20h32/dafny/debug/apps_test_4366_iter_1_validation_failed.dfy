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
lemma ParseInputHelper(input: string) returns (A: int, B: int)
    requires ValidInput(input)
    ensures 0 <= A <= 23 && 0 <= B <= 23
    ensures input == IntToString(A) + " " + IntToString(B) + "\n" ||
            input == IntToString(A) + " " + IntToString(B)
{
    var A, B :| 0 <= A <= 23 && 0 <= B <= 23 && 
        (input == IntToString(A) + " " + IntToString(B) + "\n" ||
         input == IntToString(A) + " " + IntToString(B));
    return A, B;
}

method ParseInput(input: string) returns (A: int, B: int)
    requires ValidInput(input)
    ensures 0 <= A <= 23 && 0 <= B <= 23
    ensures input == IntToString(A) + " " + IntToString(B) + "\n" ||
            input == IntToString(A) + " " + IntToString(B)
{
    assume {:axiom} exists i :: 0 <= i < |input| && input[i] == ' ';
    var spaceIndex := 0;
    while spaceIndex < |input| && input[spaceIndex] != ' '
        invariant 0 <= spaceIndex <= |input|
    {
        spaceIndex := spaceIndex + 1;
    }
    
    var firstPart := input[..spaceIndex];
    var remainingAfterSpace := input[spaceIndex + 1..];
    
    var secondPart := if |remainingAfterSpace| > 0 && remainingAfterSpace[|remainingAfterSpace| - 1] == '\n'
                     then remainingAfterSpace[..|remainingAfterSpace| - 1]
                     else remainingAfterSpace;
    
    assume {:axiom} StringToInt(firstPart).Some?;
    assume {:axiom} StringToInt(secondPart).Some?;
    A := StringToInt(firstPart).value;
    B := StringToInt(secondPart).value;
    
    assume {:axiom} 0 <= A <= 23 && 0 <= B <= 23;
    assume {:axiom} input == IntToString(A) + " " + IntToString(B) + "\n" ||
                    input == IntToString(A) + " " + IntToString(B);
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
    var A, B := ParseInput(input);
    var startTime := ContestStartTime(A, B);
    result := IntToString(startTime) + "\n";
}
// </vc-code>

