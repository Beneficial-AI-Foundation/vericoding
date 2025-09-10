predicate ValidInput(s: string)
{
    |s| >= 1 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function ExpectedLength(s: string): nat
{
    (|s| + 1) / 2
}

predicate CorrectExtraction(s: string, result: string)
{
    |result| == ExpectedLength(s) &&
    forall i :: 0 <= i < |result| ==> 0 <= 2*i < |s| && result[i] == s[2*i] &&
    forall i :: 0 <= i < |s| && i % 2 == 0 ==> exists j :: 0 <= j < |result| && result[j] == s[i] && j == i / 2
}

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures CorrectExtraction(s, result)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := "";
  while i < |s|
    invariant 0 <= i <= |s| + 1
    invariant i == 2 * |result|
    invariant forall j :: 0 <= j < |result| ==> 0 <= 2*j < |s| && result[j] == s[2*j]
    decreases |s| + 1 - i
  {
    result := result + s[i..i+1];
    i := i + 2;
  }
  assert forall j :: 0 <= j < |result| ==> 0 <= 2*j < |s| && result[j] == s[2*j];
  assert i >= |s| && i <= |s| + 1;
  assert |result| == (i + 1) / 2;
  if i == |s| {
    assert (i + 1) / 2 == (|s| + 1) / 2;
  } else {
    assert i == |s| + 1;
    assert (i + 1) / 2 == (|s| + 1) / 2;
  }
  assert |result| == ExpectedLength(s);
}
// </vc-code>

