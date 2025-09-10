predicate ValidInput(input: string)
{
    |input| > 0
}

function CanMakeSum(n: int, l: int, r: int): bool
{
    l > 0 && l <= r && n > 0 && n % l <= (r - l) * (n / l)
}

predicate ValidOutput(result: string)
{
    |result| >= 0 && forall i :: 0 <= i < |result| ==> result[i] in "Yes\nNo\n "
}

predicate CorrectSolution(input: string, result: string)
{
    var lines := SplitLines(input);
    |lines| > 0 ==> 
    (var t := ParseInt(lines[0]);
     var outputLines := SplitLines(result);
     |outputLines| >= 1 && (|outputLines| == 1 ==> outputLines[0] == "") &&
     (|outputLines| > 1 ==> outputLines[|outputLines|-1] == "") &&
     forall i :: 1 <= i <= t && i < |lines| ==>
        (var parts := SplitSpaces(lines[i]);
         |parts| >= 3 ==>
         (var n := ParseInt(parts[0]);
          var l := ParseInt(parts[1]);
          var r := ParseInt(parts[2]);
          var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
          i-1 < |outputLines| && outputLines[i-1] == expectedOutput)))
}

// <vc-helpers>
lemma CanMakeSumLemma(n: int, l: int, r: int)
  requires l > 0 && l <= r && n >= 0
  ensures CanMakeSum(n, l, r) == (n >= l && (n % l == 0 || n % l <= (r - l) * (n / l)))
{
}

function SplitLines(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var idx := FindNewline(s, 0);
    if idx == -1 then [s]
    else [s[0..idx]] + SplitLines(s[idx+1..])
}

function FindNewline(s: string, pos: int): int
  requires 0 <= pos <= |s|
  decreases |s| - pos
{
  if pos == |s| then -1
  else if s[pos] == '\n' then pos
  else FindNewline(s, pos+1)
}

function SplitSpaces(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else
    var start := SkipSpaces(s, 0);
    if start == |s| then []
    else
      var end := FindSpace(s, start);
      [s[start..end]] + SplitSpaces(s[end..])
}

function SkipSpaces(s: string, pos: int): int
  requires 0 <= pos <= |s|
  decreases |s| - pos
{
  if pos < |s| && s[pos] == ' ' then SkipSpaces(s, pos+1)
  else pos
}

function FindSpace(s: string, pos: int): int
  requires 0 <= pos <= |s|
  decreases |s| - pos
{
  if pos == |s| then |s|
  else if s[pos] == ' ' then pos
  else FindSpace(s, pos+1)
}

function ParseInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] in "0123456789" then 
    (var digit := s[0] as int - '0' as int;
     var power := 1;
     var k := |s| - 1;
     while k > 0
       decreases k
       invariant power >= 1
     {
       power := power * 10;
       k := k - 1;
     }
     digit * power + ParseInt(s[1..]))
  else 0
}

function SeqContains(s: seq<char>, pattern: string): bool
  requires |pattern| > 0
{
  if |s| < |pattern| then false
  else if s[0..|pattern|] == pattern then true
  else SeqContains(s[1..], pattern)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectSolution(input, result)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var t := ParseInt(lines[0]);
  var output := "";
  var i := 1;
  while i <= t && i < |lines|
    invariant 1 <= i <= |lines| + 1
    invariant |output| >= 0
    invariant forall j :: 0 <= j < i-1 ==> SeqContains(output, "Yes\n") || SeqContains(output, "No\n")
  {
    var parts := SplitSpaces(lines[i]);
    if |parts| >= 3 {
      var n := ParseInt(parts[0]);
      var l := ParseInt(parts[1]);
      var r := ParseInt(parts[2]);
      if l > 0 && l <= r && n > 0 && n % l <= (r - l) * (n / l) {
        output := output + "Yes\n";
      } else {
        output := output + "No\n";
      }
    }
    i := i + 1;
  }
  result := output;
}
// </vc-code>

