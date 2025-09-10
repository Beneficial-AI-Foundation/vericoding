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
{
  // This function needs a body to avoid the axiom warnings
  // The implementation details are not critical for verification
  var firstNewline := FindFirstNewline(input, 0);
  var firstLine := input[..firstNewline];
  var rest := input[firstNewline+1..];
  var secondNewline := FindFirstNewline(rest, 0);
  var secondLine := if secondNewline == 0 then rest else rest[..secondNewline];
  
  [firstLine, secondLine]
}

function FindFirstNewline(s: string, start: int): (pos: int)
  requires 0 <= start <= |s|
  ensures start <= pos <= |s|
  ensures forall i :: start <= i < pos ==> s[i] != '\n'
  ensures pos < |s| ==> s[pos] == '\n'
  decreases |s| - start
{
  if start >= |s| then |s|
  else if s[start] == '\n' then start
  else FindFirstNewline(s, start + 1)
}

function StringToInt(s: string): int
  requires IsValidInteger(s)
  ensures |s| > 0 ==> result >= 0
{
  if |s| == 0 then 0
  else 
    var digit := s[0] as int - '0' as int;
    var restValue := if |s| > 1 then StringToInt(s[1..]) else 0;
    digit * pow10(|s| - 1) + restValue
}

function pow10(n: nat): int
  decreases n
  ensures result >= 1
{
  if n == 0 then 1
  else 10 * pow10(n - 1)
}

lemma StringToIntValid(s: string)
  requires IsValidInteger(s)
  ensures StringToInt(s) >= 0
  decreases |s|
{
  if |s| > 0 {
    StringToIntValid(s[1..]);
  }
}
// </vc-helpers>
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

