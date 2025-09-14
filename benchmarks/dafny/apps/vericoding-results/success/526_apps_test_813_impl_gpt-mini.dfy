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
function SplitLines(s: string): seq<string> {
  []
}

function SplitSpaces(s: string): seq<string> {
  []
}

function ParseInt(s: string): int {
  0
}

function ParseIntSeq(ss: seq<string>): seq<int> {
  []
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
  if (!ValidInput(input)) {
    return [];
  }

  var lines := SplitLines(input);
  var n := ParseInt(SplitSpaces(lines[0])[0]);
  var arthurApples := ParseIntSeq(SplitSpaces(lines[1]));

  var len := 2 * n - 1;
  var a := new char[len];

  var k := 1;
  while k <= n
    decreases n - k + 1
  {
    var pos := 2*(k-1);

    var found := false;
    var j := 0;
    while j < |arthurApples|
      decreases |arthurApples| - j
    {
      if arthurApples[j] == k {
        found := true;
      }
      j := j + 1;
    }

    if k < n {
      a[pos+1] := ' ';
    }

    if found {
      a[pos] := '1';
    } else {
      a[pos] := '2';
    }

    // Relate found to membership for the verifier
    assert found <==> (exists t :: 0 <= t < |arthurApples| && arthurApples[t] == k);

    k := k + 1;
  }

  return a[..];
}
// </vc-code>

