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
function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[0] == '\n' then [""] + SplitLines(s[1..])
    else SplitLinesHelper(s, 0, "")
}

function SplitLinesHelper(s: string, i: int, current: string): seq<string>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then [current]
    else if s[i] == '\n' then [current] + SplitLinesHelper(s, i+1, "")
    else SplitLinesHelper(s, i+1, current + [s[i]])
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else 10 * StringToInt(s[0..|s|-1]) + (s[|s|-1] as int - '0' as int)
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

