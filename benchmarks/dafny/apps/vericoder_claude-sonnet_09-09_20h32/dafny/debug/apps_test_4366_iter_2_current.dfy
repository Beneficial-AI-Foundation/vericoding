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
lemma SplitInputLemma(input: string, A: int, B: int)
    requires 0 <= A <= 23 && 0 <= B <= 23
    requires input == IntToString(A) + " " + IntToString(B) + "\n" || input == IntToString(A) + " " + IntToString(B)
    ensures exists parts: seq<string> :: |parts| >= 2 && parts[0] == IntToString(A) && parts[1] == IntToString(B)
{
    var parts := [IntToString(A), IntToString(B)];
    assert |parts| >= 2;
    assert parts[0] == IntToString(A);
    assert parts[1] == IntToString(B);
}

lemma ParseIntLemma(s: string, val: int)
    requires s == IntToString(val)
    requires 0 <= val <= 23
    ensures StringToInt(s) == val
{
}

lemma ModuloLemma(A: int, B: int)
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= (A + B) % 24 <= 23
{
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
    
    var contestTime := ContestStartTime(A, B);
    result := IntToString(contestTime) + "\n";
    
    assert result == IntToString(ContestStartTime(A, B)) + "\n";
    assert CorrectOutput(input, result);
}
// </vc-code>

