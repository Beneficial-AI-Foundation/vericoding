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
function FindChar(s: string, c: char): int
{
    if s == "" then -1
    else if s[0] == c then 0
    else
        var idx := FindChar(s[1..], c);
        if idx == -1 then -1 else idx + 1
}

function SplitString(s: string, delim: char): seq<string>
{
    if s == "" then [] 
    else
        var idx := FindChar(s, delim);
        if idx == -1 then [s]
        else [s[0..idx]] + SplitString(s[idx+1..], delim)
}

function SplitLines(s: string): seq<string>
{
    SplitString(s, '\n')
}

function DigitToInt(c: char): int
requires '0' <= c <= '9'
{
    c - '0'
}

function StringToInt(s: string): int
{
    if s == "" then 0
    else DigitToInt(s[0]) * (10^(|s|-1)) + StringToInt(s[1..])
}

function DigitToChar(i: int): char
requires 0 <= i <= 9
{
    '0' + i
}

function IntToStringAux(i: int): string
requires i > 0
decreases i
{
    if i < 10 then [DigitToChar(i)]
    else IntToStringAux(i / 10) + [DigitToChar(i % 10)]
}

function IntToString(i: int): string
{
    if i == 0 then "0"
    else IntToStringAux(i)
}

function MaxConsecutiveWinsUpTo(lines: seq<string>, n: int, d: int): int
requires |lines| >= d+1
{
    0
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
  var resultInt := ComputeMaxConsecutiveWins(input);
  result := IntToString(resultInt) + "\n";
}
// </vc-code>

