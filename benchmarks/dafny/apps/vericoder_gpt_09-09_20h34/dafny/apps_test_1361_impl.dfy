predicate ValidInput(holds: seq<int>) {
    |holds| >= 3 && forall i :: 0 <= i < |holds| - 1 ==> holds[i] < holds[i + 1]
}

function maxDiff(s: seq<int>): int
    requires |s| >= 2
    ensures maxDiff(s) >= 0
{
    if |s| <= 1 then 0
    else
        var maxSoFar := if s[1] - s[0] >= 0 then s[1] - s[0] else 0;
        maxDiffHelper(s, 2, maxSoFar)
}

function maxDiffHelper(s: seq<int>, index: int, currentMax: int): int
    requires 1 <= index <= |s|
    requires currentMax >= 0
    ensures maxDiffHelper(s, index, currentMax) >= currentMax
    decreases |s| - index
{
    if index >= |s| then currentMax
    else
        var diff := s[index] - s[index - 1];
        var newMax := if diff > currentMax then diff else currentMax;
        maxDiffHelper(s, index + 1, newMax)
}

// <vc-helpers>
lemma LenAfterDeletionAtMiddle(s: seq<int>, j: int)
  requires |s| >= 3
  requires 1 <= j < |s| - 1
  ensures |s[..j] + s[j+1..]| == |s| - 1
{
  assert 0 <= j <= |s|;
  assert 0 <= j + 1 <= |s|;
  assert |s[..j]| == j;
  assert |s[j+1..]| == |s| - (j + 1);
  assert |s[..j] + s[j+1..]| == |s[..j]| + |s[j+1..]|;
  assert |s[..j] + s[j+1..]| == j + (|s| - (j + 1));
  assert j + (|s| - (j + 1)) == |s| - 1;
}
// </vc-helpers>

// <vc-spec>
method solve(holds: seq<int>) returns (result: int)
    requires ValidInput(holds)
    ensures result >= 0
    ensures exists k :: 1 <= k < |holds| - 1 && result == maxDiff(holds[..k] + holds[k+1..])
    ensures forall k :: 1 <= k < |holds| - 1 ==> result <= maxDiff(holds[..k] + holds[k+1..])
// </vc-spec>
// <vc-code>
{
  var n := |holds|;
  var bestK := 1;
  LenAfterDeletionAtMiddle(holds, 1);
  assert |holds[..1] + holds[2..]| >= 2;
  var bestVal := maxDiff(holds[..1] + holds[2..]);
  var i := 2;
  while i < n - 1
    invariant 1 <= i <= n - 1
    invariant 1 <= bestK < i
    invariant bestVal == maxDiff(holds[..bestK] + holds[bestK+1..])
    invariant bestVal >= 0
    invariant forall k :: 1 <= k < i ==> bestVal <= maxDiff(holds[..k] + holds[k+1..])
    decreases n - 1 - i
  {
    LenAfterDeletionAtMiddle(holds, i);
    assert |holds[..i] + holds[i+1..]| >= 2;
    var val := maxDiff(holds[..i] + holds[i+1..]);
    if val < bestVal {
      bestVal := val;
      bestK := i;
    }
    assert bestVal <= val;
    i := i + 1;
  }
  assert i == n - 1;
  result := bestVal;
}
// </vc-code>

