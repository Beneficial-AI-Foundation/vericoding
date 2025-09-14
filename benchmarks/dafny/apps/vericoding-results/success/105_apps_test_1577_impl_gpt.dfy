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
function firstNewlinePos(s: string): int
  decreases |s|
  ensures firstNewlinePos(s) == -1 || (0 <= firstNewlinePos(s) < |s| && s[firstNewlinePos(s)] == '\n')
{
  if |s| == 0 then -1
  else if s[0] == '\n' then 0
  else
    var r := firstNewlinePos(s[1..]);
    if r == -1 then -1 else 1 + r
}

function SplitLines(s: string): seq<string>
{
  var i := firstNewlinePos(s);
  if i == -1 then [s] else [s[..i], s[i+1..]]
}

function DigitVal(c: char): int
  requires c >= '0' && c <= '9'
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else 9
}

function StringToInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else 10 * StringToInt(s[..|s|-1]) + (if s[|s|-1] >= '0' && s[|s|-1] <= '9' then DigitVal(s[|s|-1]) else 0)
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
  result := DetermineWinner(CountChar(s, 'A'), CountChar(s, 'D'));
}
// </vc-code>

