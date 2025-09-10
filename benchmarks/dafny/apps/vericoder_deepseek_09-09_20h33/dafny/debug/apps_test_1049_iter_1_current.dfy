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
lemma MaxConsecutiveWinsUpToLemma(lines: seq<string>, n: int, d: int)
  requires InputWellFormed(input)
  requires var firstLineParts := SplitString(lines[0], ' ');
           var n := StringToInt(firstLineParts[0]);
           var d := StringToInt(firstLineParts[1]);
  ensures MaxConsecutiveWinsUpTo(lines, n, d) >= 0
{
}

function MaxConsecutiveWinsUpTo(lines: seq<string>, n: int, d: int): int
  requires |lines| >= 1
  requires var firstLineParts := SplitString(lines[0], ' ');
           |firstLineParts| == 2 &&
           IsValidInt(firstLineParts[0]) &&
           IsValidInt(firstLineParts[1]) &&
           var n := StringToInt(firstLineParts[0]);
           var d := StringToInt(firstLineParts[1]);
           n >= 0 && d >= 0 &&
           |lines| >= d + 1 &&
           forall i :: 1 <= i <= d ==> i < |lines| && IsValidBinaryString(lines[i], n)
{
  if d == 0 then
    0
  else
    var currentWins := CountConsecutiveWins(lines[1], n);
    var maxRest := MaxConsecutiveWinsUpTo(lines, n, d - 1);
    if currentWins > maxRest then currentWins else maxRest
}

function CountConsecutiveWins(s: string, n: int): int
  requires IsValidBinaryString(s, n)
{
  if n == 0 then
    0
  else
    var current := if s[0] == '1' then 1 else 0;
    var rest := CountConsecutiveWins(s[1..], n - 1);
    if s[0] == '1' then current + rest else 0
}

lemma SplitLinesLemma(s: string)
  ensures |SplitLines(s)| >= 0

lemma SplitStringLemma(s: string, sep: char)
  ensures |SplitString(s, sep)| >= 0

lemma StringToIntLemma(s: string)
  requires IsValidInt(s)
  ensures StringToInt(s) >= 0
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
  
  var maxWins := 0;
  var i := 1;
  
  while i <= d
    invariant 1 <= i <= d + 1
    invariant maxWins >= 0
    invariant maxWins == (if i > 1 then MaxConsecutiveWinsUpTo(lines, n, i - 1) else 0)
  {
    var currentLine := lines[i];
    var currentWins := CountConsecutiveWins(currentLine, n);
    
    if currentWins > maxWins {
      maxWins := currentWins;
    }
    
    i := i + 1;
  }
  
  result := IntToString(maxWins) + "\n";
}
// </vc-code>

