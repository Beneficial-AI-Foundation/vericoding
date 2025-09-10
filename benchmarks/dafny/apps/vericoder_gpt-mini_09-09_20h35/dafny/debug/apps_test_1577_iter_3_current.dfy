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
function IndexOfNewline(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == '\n' then 0
  else 1 + IndexOfNewline(s[1..])
}

function SplitLines(input: string): seq<string>
{
  [ input[..IndexOfNewline(input)],
    if IndexOfNewline(input) + 1 <= |input| then input[IndexOfNewline(input) + 1..] else "" ]
}

function DigitValue(c: char): int
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

function Pow10(n: int): int
  decreases n
{
  if n <= 0 then 1 else 10 * Pow10(n - 1)
}

function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function StringToInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else DigitValue(s[0]) * Pow10(|s| - 1) + StringToInt(s[1..])
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
  var countA := 0;
  var countD := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant countA == CountChar(s[..i], 'A')
    invariant countD == CountChar(s[..i], 'D')
  {
    if s[i] == 'A' {
      countA := countA + 1;
    } else {
      countD := countD + 1;
    }
    i := i + 1;
  }
  result := DetermineWinner(countA, countD);
}
// </vc-code>

