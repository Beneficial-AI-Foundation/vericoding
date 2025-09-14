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
  var i := 2;
  var best := maxDiff(holds[..1] + holds[2..]);
  ghost var bestK: int := 1;
  while i < n - 1
    invariant 2 <= i <= n - 1
    invariant 1 <= bestK < i
    invariant best == maxDiff(holds[..bestK] + holds[bestK + 1..])
    invariant forall k :: 1 <= k < i ==> best <= maxDiff(holds[..k] + holds[k + 1..])
    invariant best >= 0
    decreases n - 1 - i
  {
    var m := maxDiff(holds[..i] + holds[i + 1..]);
    if m < best {
      best := m;
      bestK := i;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>

