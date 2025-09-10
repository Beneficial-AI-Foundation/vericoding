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
function SplitLines(input: string): (lines: seq<string>)
  requires ValidInput(input)
  ensures |lines| >= 2
  ensures IsValidInteger(lines[0])
  ensures IsValidGameString(lines[1])
  ensures var n := StringToInt(lines[0]);
          var s := lines[1];
          |s| == n && n >= 1

function StringToInt(s: string): int
  requires IsValidInteger(s)
{
  if |s| == 0 then 0
  else (s[0] as int - '0' as int) * pow10(|s| - 1) + StringToInt(s[1..])
}

function pow10(n: nat): int
  decreases n
{
  if n == 0 then 1
  else 10 * pow10(n - 1)
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
  
  if countA > countD {
    result := "Anton";
  } else if countD > countA {
    result := "Danik";
  } else {
    result := "Friendship";
  }
}
// </vc-code>

