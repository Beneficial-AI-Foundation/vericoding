predicate InputWellFormed(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 1 &&
    var firstLineParts := SplitString(lines[0], ' ');
    |firstLineParts| == 2 &&
    IsValidInt(firstLineParts[0]) &&
    IsValidInt(firstLineParts[1]) &&
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);
    n >= 0 && d >= 0 &&
    |lines| >= d + 1 &&
    forall i :: 1 <= i <= d ==> i < |lines| && IsValidBinaryString(lines[i], n)
}

function ComputeMaxConsecutiveWins(input: string): int
    requires InputWellFormed(input)
{
    var lines := SplitLines(input);
    var firstLineParts := SplitString(lines[0], ' ');
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);
    MaxConsecutiveWinsUpTo(lines, n, d)
}

predicate IsValidInt(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidBinaryString(s: string, expectedLength: int)
{
    |s| == expectedLength && forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
{
    SplitString(s, '\n')
}

function SplitString(s: string, delimiter: char): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else
        var index := FindDelimiter(s, delimiter, 0);
        if index == -1 then [s]
        else if index == 0 then SplitString(s[1..], delimiter)
        else [s[..index]] + SplitString(s[index+1..], delimiter)
}

function FindDelimiter(s: string, delimiter: char, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= FindDelimiter(s, delimiter, start) < |s|
    ensures FindDelimiter(s, delimiter, start) >= 0 ==> FindDelimiter(s, delimiter, start) >= start
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == delimiter then start
    else FindDelimiter(s, delimiter, start + 1)
}

function StringToInt(s: string): int
    requires IsValidInt(s)
    ensures StringToInt(s) >= 0
    decreases |s|
{
    if |s| == 1 then (s[0] - '0') as int
    else StringToInt(s[..|s|-1]) * 10 + (s[|s|-1] - '0') as int
}

function IntToString(n: int): string
    requires n >= 0
    decreases n
{
    if n == 0 then "0"
    else if n < 10 then [(n as char + '0')]
    else IntToString(n / 10) + [(n % 10) as char + '0']
}

function MaxConsecutiveOnes(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
    ensures MaxConsecutiveOnes(s) >= 0
{
    MaxConsecutiveOnesFrom(s, 0, 0, 0)
}

function MaxConsecutiveOnesFrom(s: string, index: int, currentCount: int, maxCount: int): int
    requires 0 <= index <= |s|
    requires currentCount >= 0
    requires maxCount >= 0
    requires forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
    ensures MaxConsecutiveOnesFrom(s, index, currentCount, maxCount) >= 0
    ensures MaxConsecutiveOnesFrom(s, index, currentCount, maxCount) >= maxCount
    ensures MaxConsecutiveOnesFrom(s, index, currentCount, maxCount) >= currentCount
    decreases |s| - index
{
    if index == |s| then 
        if currentCount > maxCount then currentCount else maxCount
    else if s[index] == '1' then
        MaxConsecutiveOnesFrom(s, index + 1, currentCount + 1, maxCount)
    else
        var newMax := if currentCount > maxCount then currentCount else maxCount;
        MaxConsecutiveOnesFrom(s, index + 1, 0, newMax)
}

function MaxConsecutiveWinsUpTo(lines: seq<string>, n: int, d: int): int
    requires |lines| >= d + 1
    requires d >= 0
    requires forall i :: 1 <= i <= d ==> i < |lines| && IsValidBinaryString(lines[i], n)
    ensures MaxConsecutiveWinsUpTo(lines, n, d) >= 0
{
    MaxConsecutiveWinsUpToHelper(lines, n, d, 1, 0)
}

function MaxConsecutiveWinsUpToHelper(lines: seq<string>, n: int, d: int, index: int, maxSoFar: int): int
    requires |lines| >= d + 1
    requires 1 <= index <= d + 1
    requires d >= 0
    requires maxSoFar >= 0
    requires forall i :: 1 <= i <= d ==> i < |lines| && IsValidBinaryString(lines[i], n)
    ensures MaxConsecutiveWinsUpToHelper(lines, n, d, index, maxSoFar) >= maxSoFar
    ensures MaxConsecutiveWinsUpToHelper(lines, n, d, index, maxSoFar) >= 0
    decreases d + 1 - index
{
    if index > d then maxSoFar
    else
        var currentMax := MaxConsecutiveOnes(lines[index]);
        var newMax := if currentMax > maxSoFar then currentMax else maxSoFar;
        MaxConsecutiveWinsUpToHelper(lines, n, d, index + 1, newMax)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires InputWellFormed(input)
    ensures result == IntToString(ComputeMaxConsecutiveWins(input)) + "\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var firstLineParts := SplitString(lines[0], ' ');
    var n := StringToInt(firstLineParts[0]);
    var d := StringToInt(firstLineParts[1]);
    
    var maxConsecutive := 0;
    var i := 1;
    
    while i <= d
        invariant 1 <= i <= d + 1
        invariant maxConsecutive >= 0
        invariant |lines| >= d + 1
        invariant forall j :: 1 <= j <= d ==> j < |lines| && IsValidBinaryString(lines[j], n)
        invariant maxConsecutive == MaxConsecutiveWinsUpToHelper(lines, n, d, 1, 0) - MaxConsecutiveWinsUpToHelper(lines, n, d, i, 0) + maxConsecutive
    {
        var currentLine := lines[i];
        var currentConsecutive := MaxConsecutiveOnes(currentLine);
        if currentConsecutive > maxConsecutive {
            maxConsecutive := currentConsecutive;
        }
        i := i + 1;
    }
    
    result := IntToString(maxConsecutive) + "\n";
}
// </vc-code>

