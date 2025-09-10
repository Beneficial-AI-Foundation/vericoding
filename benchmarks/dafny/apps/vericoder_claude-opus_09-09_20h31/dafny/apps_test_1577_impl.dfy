predicate ValidInput(input: string)
{
    |input| > 0 && exists newlinePos :: 0 <= newlinePos < |input| && input[newlinePos] == '\n'
}

predicate ValidParsedInput(lines: seq<string>)
{
    |lines| >= 2 && IsValidInteger(lines[0]) && IsValidGameString(lines[1]) &&
    var n := StringToInt(lines[0]);
    var s := lines[1];
    |s| == n && n >= 1
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
}

predicate IsValidGameString(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == 'A' || s[i] == 'D'
}

function CountChar(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function DetermineWinner(countA: int, countD: int): string
{
    if countA > countD then "Anton"
    else if countD > countA then "Danik"  
    else "Friendship"
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
    requires ValidInput(input)
    ensures |SplitLines(input)| >= 2
{
    var newlinePos := FindNewline(input, 0);
    [input[..newlinePos], input[newlinePos+1..]]
}

function FindNewline(input: string, i: int): int
    requires 0 <= i <= |input|
    requires exists j :: i <= j < |input| && input[j] == '\n'
    ensures i <= FindNewline(input, i) < |input|
    ensures input[FindNewline(input, i)] == '\n'
    ensures forall k :: i <= k < FindNewline(input, i) ==> input[k] != '\n'
    decreases |input| - i
{
    if i < |input| && input[i] == '\n' then
        i
    else
        FindNewline(input, i + 1)
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
    ensures StringToInt(s) >= 0
{
    if |s| == 1 then
        (s[0] - '0') as int
    else
        StringToInt(s[..|s|-1]) * 10 + (s[|s|-1] - '0') as int
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    requires ValidParsedInput(SplitLines(input))
    ensures result == "Anton" || result == "Danik" || result == "Friendship"
    ensures var lines := SplitLines(input);
            var s := lines[1];
            var countA := CountChar(s, 'A');
            var countD := CountChar(s, 'D');
            result == DetermineWinner(countA, countD)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var s := lines[1];
    var countA := CountChar(s, 'A');
    var countD := CountChar(s, 'D');
    result := DetermineWinner(countA, countD);
}
// </vc-code>

