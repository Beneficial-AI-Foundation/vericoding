predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && |SplitSpaces(lines[0])| >= 3 &&
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    n > 0
}

predicate ValidOutput(input: string, result: seq<char>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    |result| == 2 * n - 1 &&
    (forall i :: 0 <= i < n ==> result[2*i] == '1' || result[2*i] == '2') &&
    (forall i :: 0 <= i < n-1 ==> result[2*i+1] == ' ')
}

predicate CorrectAssignment(input: string, result: seq<char>)
    requires ValidInput(input)
    requires ValidOutput(input, result)
{
    var lines := SplitLines(input);
    var n := ParseInt(SplitSpaces(lines[0])[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    forall i :: 1 <= i <= n ==> 
        (i in arthurSet ==> result[2*(i-1)] == '1') &&
        (i !in arthurSet ==> result[2*(i-1)] == '2')
}

// <vc-helpers>
// Helper function to split string by newline characters
function SplitLines(s: string): seq<string>
{
  if s == "" then [] else
  var idx := s.IndexOf('\n');
  if idx == -1 then [s] else [s[..idx]] + SplitLines(s[idx+1..])
}

// Helper function to split string by space characters
function SplitSpaces(s: string): seq<string>
{
  if s == "" then [] else
  var idx := s.IndexOf(' ');
  if idx == -1 then [s] else [s[..idx]] + SplitSpaces(s[idx+1..]).Filter(x => x != "")
}

// Helper function to parse integer from string
function ParseInt(s: string): int
  requires forall i :: 0 <= i < |s| ==> s[i] in "0123456789-"
  // Assume valid digits
{
  if |s| == 0 then 0 else
  if s[0] == '-' then -ParseInt(s[1..]) else
  if |s| == 1 then (s[0] - '0') else
  (s[0] - '0') * Power(10, |s|-1) + ParseInt(s[1..])
}

// Helper function for power (used in ParseInt if base 10)
function Power(base: int, exp: nat): int
{
  if exp == 0 then 1 else base * Power(base, exp-1)
}

// Helper function to parse sequence of ints from seq<string>
function ParseIntSeq(ss: seq<string>): seq<int>
{
  if ss == [] then [] else [ParseInt(ss[0])] + ParseIntSeq(ss[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<char>)
    requires |input| > 0
    ensures !ValidInput(input) ==> |result| == 0
    ensures ValidInput(input) ==> ValidOutput(input, result) && CorrectAssignment(input, result)
    ensures forall i :: 0 <= i < |result| ==> result[i] == '1' || result[i] == '2' || result[i] == ' '
// </vc-spec>
// <vc-code>
{
  if !ValidInput(input) {
    result := [];
  } else {
    var lines := SplitLines(input);
    var firstLineParts := SplitSpaces(lines[0]);
    var n := ParseInt(firstLineParts[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;
    result := [];
    var i := 1;
    while i <= n
      invariant 1 <= i <= n+1
      invariant |result| == 2*(i-1) - 1 + (if i > 1 then 1 else 0)
      invariant forall k :: 1 <= k < i ==> 
        (k in arthurSet ==> result[2*(k-1)] == '1') &&
        (k !in arthurSet ==> result[2*(k-1)] == '2') &&
        (k < i-1 ==> result[2*k-1] == ' ')
      invariant forall j :: 0 <= j < |result| ==> result[j] == '1' || result[j] == '2' || result[j] == ' '
    {
      var charToAdd := if i in arthurSet then '1' else '2';
      if i > 1 {
        result := result + [' '] + [charToAdd];
      } else {
        result := result + [charToAdd];
      }
      i := i + 1;
    }
  }
}
// </vc-code>

