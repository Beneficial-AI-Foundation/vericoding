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
{
    SplitStringHelper(s, delimiter, 0, 0, [])
}

function SplitStringHelper(s: string, delimiter: char, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= current <= |s|
    decreases |s| - current
{
    if current >= |s| then
        if start < |s| then acc + [s[start..|s|]] else acc
    else if s[current] == delimiter then
        SplitStringHelper(s, delimiter, current + 1, current + 1, acc + [s[start..current]])
    else
        SplitStringHelper(s, delimiter, start, current + 1, acc)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, index: int): int
    requires IsValidInteger(s)
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index >= |s| then 0
    else (s[index] - '0') as int * Power10(|s| - index - 1) + StringToIntHelper(s, index + 1)
}

function Power10(n: nat): nat
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
    decreases n
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [(n % 10) as char + '0']
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures CorrectResult(input, result)
// </vc-spec>
// <vc-code>
{
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
    
    var minCost := MinimumCost(n, a, b);
    result := IntToString(minCost) + "\n";
}
// </vc-code>

