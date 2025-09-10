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
function FindNewlineIndex(s: string): (idx: int)
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == '\n' then 0
  else 
    var idx_rest := FindNewlineIndex(s[1..]);
    if idx_rest == -1 then -1 else idx_rest + 1
}

function SplitLines(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else 
    var idx := FindNewlineIndex(s);
    if idx == -1 then [s]
    else [s[..idx]] + SplitLines(s[idx+1..])
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
  requires IsValidInteger(s)
  decreases |s|
{
  if |s| == 0 then acc
  else 
    var digit := ord(s[0]) - ord('0');
    StringToIntHelper(s[1..], acc * 10 + digit)
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
  return DetermineWinner(countA, countD);
}
// </vc-code>

