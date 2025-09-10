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
// Added no helpers; all proof done inside method body.
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
    // i < |s| ensures s[i..i+1] is well-defined
    result := result + s[i..i+1];
    i := i + 2;
  }
  // From the loop invariants we have the mapping property for all indices of result
  assert forall j :: 0 <= j < |result| ==> 0 <= 2*j < |s| && result[j] == s[2*j];
  // And bounds on i
  assert i >= |s| && i <= |s| + 1;
  // Relate |result| and i
  assert |result| == i / 2;
  // Show |result| equals ExpectedLength(s)
  if i == |s| {
    assert i / 2 == (|s| + 1) / 2;
  } else {
    // i == |s| + 1
    assert i == |s| + 1;
    assert i / 2 == (|s| + 1) / 2;
  }
  assert |result| == ExpectedLength(s);

  // Finally prove that every even-indexed character of s appears in result at index i/2.
  assert forall k :: 0 <= k < |s| && k % 2 == 0 ==>
    (exists j :: 0 <= j < |result| && result[j] == s[k] && j == k / 2)
  {
    var j := k / 2;
    // k is even, so k == 2*j
    assert 2 * j == k;
    // k < |s| and i >= |s| imply k < i, hence 2*j < i
    assert k < i;
    assert 2 * j < i;
    // i == 2*|result| gives j < |result|
    assert i == 2 * |result|;
    assert 2 * j < 2 * |result|;
    assert j < |result|;
    // mapping invariant gives result[j] == s[2*j] == s[k]
    assert result[j] == s[2*j];
    assert result[j] == s[k];
    // produce the existential witness
    assert exists j' :: 0 <= j' < |result| && result[j'] == s[k] && j' == k / 2;
  }

  // All parts of CorrectExtraction are now established
}
// </vc-code>

