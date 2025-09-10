predicate ValidInput(s: string) {
    var lines := SplitByNewlines(s);
    |lines| >= 3 &&
    IsPositiveInteger(lines[0]) &&
    IsPositiveInteger(lines[1]) &&
    var n := StringToInt(lines[0]);
    var k := StringToInt(lines[1]);
    1 <= n <= 100 &&
    1 <= k <= 100 &&
    IsValidXArray(lines[2], n, k)
}

predicate ValidOutput(result: string) {
    |result| >= 2 &&
    result[|result|-1] == '\n' &&
    IsNonNegativeInteger(result[..|result|-1])
}

predicate CorrectSolution(input: string, output: string) {
    ValidInput(input) && ValidOutput(output) ==>
        var lines := SplitByNewlines(input);
        var n := StringToInt(lines[0]);
        var k := StringToInt(lines[1]);
        var x := ParseIntArray(lines[2]);
        |x| == n &&
        (forall i :: 0 <= i < n ==> 0 < x[i] < k) &&
        var expectedSum := ComputeMinDistance(x, k);
        StringToInt(output[..|output|-1]) == expectedSum
}

predicate IsPositiveInteger(s: string) {
    IsNonNegativeInteger(s) && |s| > 0 && (|s| > 1 || s[0] != '0') && StringToInt(s) > 0
}

predicate IsNonNegativeInteger(s: string) {
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidXArray(s: string, n: int, k: int) {
    var x := ParseIntArray(s);
    |x| == n && forall i :: 0 <= i < n ==> 0 < x[i] < k
}

function ComputeMinDistance(x: seq<int>, k: int): int
    requires forall i :: 0 <= i < |x| ==> 0 < x[i] < k
    ensures ComputeMinDistance(x, k) >= 0
{
    Sum(seq(|x|, i requires 0 <= i < |x| => 2 * Min(k - x[i], x[i])))
}

// <vc-helpers>
function SplitByNewlines(s: string): seq<string>
{
    if (|s| == 0) then []
    else
        var firstNewline := -1;
        for i := 0 to |s| - 1
            invariant -1 <= firstNewline <= i
            invariant (forall j :: 0 <= j < i ==> s[j] != '\n') ==> firstNewline == -1
            invariant (exists j :: 0 <= j < i && s[j] == '\n') ==> firstNewline != -1 && s[firstNewline] == '\n'
        {
            if (s[i] == '\n')
            {
                firstNewline := i;
                break;
            }
        }
        if (firstNewline == -1) then [s]
        else if (firstNewline == 0) then SplitByNewlines(s[1..]) // Handle leading newline
        else [s[..firstNewline]] + SplitByNewlines(s[firstNewline+1..])
}

function StringToInt(s: string): int
requires IsNonNegativeInteger(s)
ensures StringToInt(s) >= 0
{
    var res := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant res == (if i == 0 then 0 else StringToInt(s[..i]))
        invariant (forall j :: 0 <= j < i ==> '0' <= s[j] <= '9')
    {
        res := res * 10 + (s[i] as int - '0' as int);
    }
    return res;
}

function ParseIntArray(s: string): seq<int>
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' || s[i] == ' '
    {
        var result: seq<int> := [];
        var currentNumStr := "";
        for i := 0 to |s|
            invariant 0 <= i <= |s|
            invariant forall j :: 0 <= j < |currentNumStr| ==> '0' <=currentNumStr[j] <= '9'
            invariant forall k :: 0 <= k < |result| ==> result[k] >= 0 // Integers are non-negative
        {
            if i < |s| && '0' <= s[i] <= '9' {
                currentNumStr := currentNumStr + s[i];
            } else {
                if |currentNumStr| > 0 {
                    result := result + [StringToInt(currentNumStr)];
                }
                currentNumStr := "";
            }
        }
        return result;
    }

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

function Min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires ValidInput(s)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures ValidOutput(result)
    ensures CorrectSolution(s, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewlines(s);
    var n := StringToInt(lines[0]);
    var k := StringToInt(lines[1]);
    var x := ParseIntArray(lines[2]);
    
    var totalDistance := ComputeMinDistance(x, k);
    
    result := (totalDistance as string) + "\n";
    
    return result;
}
// </vc-code>

