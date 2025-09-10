predicate ValidInput(n: int, a: int, b: int)
{
    1 <= n <= 20 && 1 <= a <= 50 && 1 <= b <= 50
}

function TrainCost(n: int, a: int): int
{
    n * a
}

function MinimumCost(n: int, a: int, b: int): int
{
    var trainCost := TrainCost(n, a);
    if trainCost < b then trainCost else b
}

predicate CorrectResult(input: string, result: string)
{
    var lines := SplitString(input, '\n');
    if |lines| > 0 then
        var parts := SplitString(lines[0], ' ');
        if |parts| >= 3 && IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2]) then
            var n := StringToInt(parts[0]);
            var a := StringToInt(parts[1]);
            var b := StringToInt(parts[2]);
            ValidInput(n, a, b) ==> result == IntToString(MinimumCost(n, a, b)) + "\n"
        else
            result == ""
    else
        result == ""
}

// <vc-helpers>
function SplitString(s: string, delimiter: char): seq<string>

function IsValidInteger(s: string): bool

function StringToInt(s: string): int
    requires IsValidInteger(s)

function IntToString(n: int): string

lemma SplitStringProperties(s: string, delimiter: char)
    ensures var parts := SplitString(s, delimiter);
            forall i :: 0 <= i < |parts| ==> delimiter !in parts[i]

lemma IntToStringProperties(n: int)
    ensures IsValidInteger(IntToString(n))
    ensures StringToInt(IntToString(n)) == n

lemma SplitStringNonEmpty(s: string, delimiter: char)
    requires |s| > 0
    ensures |SplitString(s, delimiter)| > 0

lemma CorrectResultHelper(input: string, result: string, lines: seq<string>, parts: seq<string>, n: int, a: int, b: int)
    requires lines == SplitString(input, '\n')
    requires |lines| > 0
    requires parts == SplitString(lines[0], ' ')
    requires |parts| >= 3
    requires IsValidInteger(parts[0]) && IsValidInteger(parts[1]) && IsValidInteger(parts[2])
    requires n == StringToInt(parts[0])
    requires a == StringToInt(parts[1])
    requires b == StringToInt(parts[2])
    requires ValidInput(n, a, b)
    requires result == IntToString(MinimumCost(n, a, b)) + "\n"
    ensures CorrectResult(input, result)
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures CorrectResult(input, result)
// </vc-spec>
// <vc-code>
{
    SplitStringNonEmpty(input, '\n');
    var lines := SplitString(input, '\n');
    if |lines| == 0 {
        return "";
    }
    
    var parts := SplitString(lines[0], ' ');
    if |parts| < 3 {
        return "";
    }
    
    if !IsValidInteger(parts[0]) || !IsValidInteger(parts[1]) || !IsValidInteger(parts[2]) {
        return "";
    }
    
    var n := StringToInt(parts[0]);
    var a := StringToInt(parts[1]);
    var b := StringToInt(parts[2]);
    
    if !ValidInput(n, a, b) {
        return "";
    }
    
    var cost := MinimumCost(n, a, b);
    IntToStringProperties(cost);
    result := IntToString(cost) + "\n";
    CorrectResultHelper(input, result, lines, parts, n, a, b);
}
// </vc-code>

