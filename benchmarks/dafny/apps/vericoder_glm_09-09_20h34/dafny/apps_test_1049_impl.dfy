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
        let idx := FindChar(s[1..], c) in
        if idx == -1 then -1 else idx + 1
}

function SplitString(s: string, delim: char): seq<string>
{
    if s == "" then [] 
    else
        let idx := FindChar(s, delim) in
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
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires InputWellFormed(input)
    ensures result == IntToString(ComputeMaxConsecutiveWins(input)) + "\n"
// </vc-spec>
// <vc-code>
function FindChar(s: string, c: char): int
{
    if s == "" then -1
    else if s[0] == c then 0
    else
        let idx := FindChar(s[1..], c) in
        if idx == -1 then -1 else idx + 1
}

function SplitString(s: string, delim: char): seq<string>
{
    if s == "" then [] 
    else
        let idx := FindChar(s, delim) in
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
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then
// </vc-code>

