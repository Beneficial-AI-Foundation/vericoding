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
function SplitLines(s: string): seq<string>
{
  [s]
}

function SplitSpaces(s: string): seq<string>
{
  [s]
}

function ParseInt(s: string): int
{
  1
}

function ParseIntSeq(ss: seq<string>): seq<int>
{
  if |ss| == 0 then []
  else [ParseInt(ss[0])] + ParseIntSeq(ss[1..])
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
    var tokens0 := SplitSpaces(lines[0]);
    var n := ParseInt(tokens0[0]);
    var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));
    var arthurSet := set x | x in arthurApples;

    var r: seq<char> := [];
    var j := 0;
    while j < 2 * n - 1
      invariant 0 <= j <= 2 * n - 1
      invariant |r| == j
      invariant forall i :: 0 <= i < j ==> r[i] == '1' || r[i] == '2' || r[i] == ' '
      invariant forall i :: 0 <= i < j ==> (i % 2 == 1 ==> r[i] == ' ')
      invariant forall t :: 0 <= t < (j + 1) / 2 ==> ((t + 1) in arthurSet ==> r[2 * t] == '1') && ((t + 1) !in arthurSet ==> r[2 * t] == '2')
      decreases 2 * n - 1 - j
    {
      if j % 2 == 1 {
        r := r + [' '];
      } else {
        if (j / 2 + 1) in arthurSet {
          r := r + ['1'];
        } else {
          r := r + ['2'];
        }
      }
      j := j + 1;
    }
    result := r;
  }
}
// </vc-code>

