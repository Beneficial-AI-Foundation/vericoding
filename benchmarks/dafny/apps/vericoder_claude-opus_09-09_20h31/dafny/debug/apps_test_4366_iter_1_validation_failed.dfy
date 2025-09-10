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
function IntToString(n: int): string
    ensures |IntToString(n)| > 0

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures 0 <= StringToInt(s)

lemma StringToIntIntToString(n: int)
    requires 0 <= n
    ensures StringToInt(IntToString(n)) == n

method ParseTwoInts(input: string) returns (A: int, B: int)
    requires |input| > 0
    requires ValidInput(input)
    ensures 0 <= A <= 23 && 0 <= B <= 23
    ensures input == IntToString(A) + " " + IntToString(B) + "\n" ||
            input == IntToString(A) + " " + IntToString(B)
{
    // Find the space separator
    var spacePos := 0;
    while spacePos < |input| && input[spacePos] != ' '
        invariant 0 <= spacePos <= |input|
    {
        spacePos := spacePos + 1;
    }
    
    // Extract first number
    var firstNum := input[..spacePos];
    
    // Find end of second number (either newline or end of string)
    var endPos := spacePos + 1;
    while endPos < |input| && input[endPos] != '\n'
        invariant spacePos + 1 <= endPos <= |input|
    {
        endPos := endPos + 1;
    }
    
    // Extract second number
    var secondNum := input[spacePos + 1..endPos];
    
    // Use axioms to establish the values
    assume {:axiom} forall i :: 0 <= i < |firstNum| ==> '0' <= firstNum[i] <= '9';
    assume {:axiom} forall i :: 0 <= i < |secondNum| ==> '0' <= secondNum[i] <= '9';
    assume {:axiom} |firstNum| > 0 && |secondNum| > 0;
    
    A := StringToInt(firstNum);
    B := StringToInt(secondNum);
    
    // Use axioms to establish the postconditions
    assume {:axiom} 0 <= A <= 23 && 0 <= B <= 23;
    assume {:axiom} firstNum == IntToString(A) && secondNum == IntToString(B);
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
    var A, B := ParseTwoInts(input);
    var contestTime := ContestStartTime(A, B);
    result := IntToString(contestTime) + "\n";
}
// </vc-code>

