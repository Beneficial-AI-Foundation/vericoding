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
  ensures forall i :: 0 <= i < |SplitLines(input)| ==> !SplitLines(input)[i].Contains('\n')
  ensures |SplitLines(input)| > 0
  decreases |input|
{
  var lines: seq<string> := [];
  var currentLineStart := 0;
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant 0 <= currentLineStart <= i
    invariant forall j :: 0 <= j < |lines| ==> !lines[j].Contains('\n')
    invariant |lines| == 0 || (currentLineStart > 0 && input[currentLineStart - 1] == '\n') || currentLineStart == 0
    invariant currentLineStart <= |input|
    invariant forall k :: 0 <= k < |lines| ==> var line := lines[k]; !line.Contains('\n')
    decreases |input| - i
  {
    if input[i] == '\n' {
      lines := lines + [input[currentLineStart .. i]];
      currentLineStart := i + 1;
    }
    i := i + 1;
  }
  lines := lines + [input[currentLineStart .. |input|]];
  return lines;
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
  ensures StringToInt(s) >= 0
{
  var n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n >= 0
    decreases |s| - i
  {
    n := n * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  return n;
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
    var n := StringToInt(lines[0]);
    var s := lines[1];

    var countA := CountChar(s, 'A');
    var countD := CountChar(s, 'D');

    result := DetermineWinner(countA, countD);
}
// </vc-code>

