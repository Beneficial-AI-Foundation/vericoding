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
function TakeUntil(ch: char, s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if s[0] == ch then ""
  else [s[0]] + TakeUntil(ch, s[1..])
}

function DropUntil(ch: char, s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if s[0] == ch then s[1..]
  else DropUntil(ch, s[1..])
}

function SplitLines(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] == '\n' then SplitLines(s[1..])
  else [TakeUntil('\n', s)] + SplitLines(s[|TakeUntil('\n', s)|..])
}

function SplitString(s: string, ch: char): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] == ch then SplitString(s[1..], ch)
  else [TakeUntil(ch, s)] + SplitString(s[|TakeUntil(ch, s)|..], ch)
}

function StringToInt(s: string): int
  requires IsValidInt(s)
  ensures 0 <= StringToInt(s)
  decreases |s|
{
  if |s| == 1 then (s[0] as int) - ('0' as int)
  else 10 * StringToInt(s[..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

function IntToString(i: int): string
  requires i >= 0
  decreases i
{
  if i < 10 then [ (('0' as int) + i) as char ]
  else IntToString(i / 10) + [ (('0' as int) + (i % 10)) as char ]
}

function MaxConsec(lines: seq<string>, i: int, k: int, current: int, maxConsec: int, n: int): int
  requires |lines| >= k + 1
  requires 0 <= i < n
  requires 0 <= k
  requires forall j :: 1 <= j <= k ==> |lines[j]| == n && (lines[j][i] == '0' || lines[j][i] == '1')
  decreases k
{
  if k == 0 then maxConsec
  else if lines[k][i] == '1' then MaxConsec(lines, i, k-1, current + 1, if current + 1 > maxConsec then current + 1 else maxConsec, n)
  else MaxConsec(lines, i, k-1, 0, maxConsec, n)
}

function MaxConsecInColumn(lines: seq<string>, i: int, n: int, d: int): int
  requires |lines| >= d + 1
  requires 0 <= i < n
  requires forall j :: 1 <= j <= d ==> |lines[j]| == n && (lines[j][i] == '0' || lines[j][i] == '1')
{
  MaxConsec(lines, i, d, 0, 0, n)
}

function MaxOverall(lines: seq<string>, n: int, d: int, currentMax: int): int
  decreases n
{
  if n == 0 then currentMax
  else MaxOverall(lines, n-1, d, if MaxConsecInColumn(lines, n-1, n, d) > currentMax then MaxConsecInColumn(lines, n-1, n, d) else currentMax)
}

function MaxConsecutiveWinsUpTo(lines: seq<string>, n: int, d: int): int
  requires |lines| >= d + 1
  requires forall i :: 1 <= i <= d ==> |lines[i]| == n
  ensures 0 <= MaxConsecutiveWinsUpTo(lines, n, d)
{
  MaxOverall(lines, n, d, 0)
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
  result := IntToString(ComputeMaxConsecutiveWins(input)) + "\n";
}
// </vc-code>

