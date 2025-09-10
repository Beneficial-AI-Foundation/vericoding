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
    var newlinePos := FindNewlinePos(input);
    [input[0..newlinePos], input[newlinePos+1..]]
}

function FindNewlinePos(input: string): int
    requires ValidInput(input)
    ensures 0 <= FindNewlinePos(input) < |input|
    ensures input[FindNewlinePos(input)] == '\n'
    decreases |input|
{
    if input[0] == '\n' then 0
    else 1 + FindNewlinePos(input[1..])
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
    ensures StringToInt(s) >= 0
    decreases |s|
{
    if |s| == 1 then (s[0] as int - '0' as int)
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
    requires IsValidInteger(s) && |s| > 1
    ensures StringToIntHelper(s) >= 0
    decreases |s|
{
    StringToIntValidSubstring(s);
    StringToInt(s[0..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

lemma StringToIntValidSubstring(s: string)
    requires IsValidInteger(s) && |s| > 1
    ensures IsValidInteger(s[0..|s|-1])
{
    assert |s[0..|s|-1]| == |s| - 1 > 0;
    forall i | 0 <= i < |s[0..|s|-1]| {:trigger s[0..|s|-1][i]}
        ensures s[0..|s|-1][i] >= '0' && s[0..|s|-1][i] <= '9'
    {
        assert s[0..|s|-1][i] == s[i];
        assert s[i] >= '0' && s[i] <= '9';
    }
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

