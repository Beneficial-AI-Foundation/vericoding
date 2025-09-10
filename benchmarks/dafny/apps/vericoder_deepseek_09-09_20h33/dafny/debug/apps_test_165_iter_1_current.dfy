function Max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function CalculateMissedMeals(input: string): int
{
    var parts := SplitSpaces(TrimNewline(input));
    if |parts| >= 3 then
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);  
        var c := StringToInt(parts[2]);
        var maxVal := Max3(a, b, c);
        var threshold := maxVal - 1;
        (if a < threshold then threshold - a else 0) +
        (if b < threshold then threshold - b else 0) +
        (if c < threshold then threshold - c else 0)
    else 0
}

predicate ValidInput(input: string)
{
    |input| > 0
}

// <vc-helpers>
predicate SplitSpacesValid(s: string)
{
    |SplitSpaces(s)| >= 0
}

predicate StringToIntValid(s: string)
{
    StringToInt(s) == StringToInt(s)  // Valid as long as it doesn't crash
}

lemma SplitSpacesPreservesContent(input: string)
ensures |SplitSpaces(input)| >= 3 ==> (SplitSpaces(input))[0] == SplitSpaces(TrimNewline(input))[0]
ensures |SplitSpaces(input)| >= 3 ==> (SplitSpaces(input))[1] == SplitSpaces(TrimNewline(input))[1]
ensures |SplitSpaces(input)| >= 3 ==> (SplitSpaces(input))[2] == SplitSpaces(TrimNewline(input))[2]
{
}

lemma Max3Properties(a: int, b: int, c: int)
ensures Max3(a, b, c) >= a
ensures Max3(a, b, c) >= b
ensures Max3(a, b, c) >= c
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
    var trimmed := TrimNewline(input);
    var parts := SplitSpaces(trimmed);
    if |parts| >= 3 {
        var a_val := StringToInt(parts[0]);
        var b_val := StringToInt(parts[1]);
        var c_val := StringToInt(parts[2]);
        var max_val := Max3(a_val, b_val, c_val);
        var threshold := max_val - 1;
        var missed1 := if a_val < threshold then threshold - a_val else 0;
        var missed2 := if b_val < threshold then threshold - b_val else 0;
        var missed3 := if c_val < threshold then threshold - c_val else 0;
        result := IntToString(missed1 + missed2 + missed3);
    } else {
        result := "0";
    }
}
// </vc-code>

