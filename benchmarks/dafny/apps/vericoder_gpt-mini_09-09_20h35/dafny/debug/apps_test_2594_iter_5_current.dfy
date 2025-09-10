predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| > 0 &&
    var t := ParseInt(lines[0]);
    t > 0 && |lines| >= t + 1 &&
    forall i {:trigger SplitSpaces(lines[i+1])} :: 0 <= i < t ==>
        var parts := SplitSpaces(lines[i+1]);
        |parts| >= 2 &&
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        n >= 1 && m >= 1
}

function MinLanterns(n: int, m: int): int
    requires n >= 1 && m >= 1
{
    (n * m + 1) / 2
}

predicate ValidOutput(input: string, output: seq<int>)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    |output| == t &&
    forall i {:trigger output[i]} :: 0 <= i < t ==>
        var parts := SplitSpaces(lines[i+1]);
        |parts| >= 2 &&
        var n := ParseInt(parts[0]);
        var m := ParseInt(parts[1]);
        n >= 1 && m >= 1 &&
        output[i] == MinLanterns(n, m)
}

// <vc-helpers>
lemma PartsNonEmpty(input: string, t: int, i: int)
  requires ValidInput(input)
  requires t == ParseInt(SplitLines(input)[0])
  requires 0 <= i < t
  ensures |SplitSpaces(SplitLines(input)[i+1])| >= 2
  ensures ParseInt(SplitSpaces(SplitLines(input)[i+1])[0]) >= 1
  ensures ParseInt(SplitSpaces(SplitLines(input)[i+1])[1]) >= 1
{
  var lines := SplitLines(input);
  var parts := SplitSpaces(lines[i+1]);
  assert |parts| >= 2;
  assert ParseInt(parts[0]) >= 1;
  assert ParseInt(parts[1]) >= 1;
}

method Solve(input: string) returns (output: seq<int>)
  requires ValidInput(input)
  ensures ValidOutput(input, output)
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(input);
  var t := ParseInt(lines[0]);
  var output: seq<int> := [];
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant |output| == i
    invariant forall j {:trigger SplitSpaces(lines[j+1])} :: 0 <= j < i ==>
      |SplitSpaces(lines[j+1])| >= 2 &&
      ParseInt(SplitSpaces(lines[j+1])[0]) >= 1 &&
      ParseInt(SplitSpaces(lines[j+1])[1]) >= 1 &&
      output[j] == MinLanterns(ParseInt(SplitSpaces(lines[j+1])[0]), ParseInt(SplitSpaces(lines[j+1])[1]))
    decreases t - i
  {
    PartsNonEmpty(input, t, i);
    var parts := SplitSpaces(lines[i+1]);
    var n := ParseInt(parts[0]);
    var m := ParseInt(parts[1]);
    var v := MinLanterns(n, m);
    output := output + [v];
    assert output[i] == v;
    i := i + 1;
  }
  return output;
}
// </vc-code>

