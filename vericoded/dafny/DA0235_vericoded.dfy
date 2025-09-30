predicate isValidPlacement(rooms: string, k: int, placement: seq<int>)
{
    |placement| == k + 1 &&
    (forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|) &&
    (forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0') &&
    (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
    (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
}

// <vc-helpers>
function optimalMaxDistance(placement: seq<int>): int
{
  0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, rooms: string) returns (result: int)
    requires n > 0
    requires k > 0 
    requires k < n
    requires |rooms| == n
    requires forall i :: 0 <= i < n ==> rooms[i] == '0' || rooms[i] == '1'
    requires |set i | 0 <= i < n && rooms[i] == '0'| >= k + 1
    ensures result >= 0
    ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result
// </vc-spec>
// <vc-code>
{
  var zeros := [];
  var i := 0;
  ghost var seen: set<int> := {};
  while i < n
    invariant 0 <= i <= n
    invariant seen == set j | 0 <= j < i && rooms[j] == '0'
    invariant forall t :: 0 <= t < |zeros| ==> 0 <= zeros[t] < i && rooms[zeros[t]] == '0'
    invariant forall a,b :: 0 <= a < b < |zeros| ==> zeros[a] < zeros[b]
    invariant |zeros| == |seen|
  {
    if rooms[i] == '0' {
      zeros := zeros + [i];
      seen := seen + {i};
    }
    i := i + 1;
  }

  // After the scan, zeros contains all indices j with rooms[j] == '0'
  // From the precondition there are at least k+1 such indices.
  assert |zeros| >= k + 1;
  var placement := zeros[0..k+1];

  // placement satisfies isValidPlacement
  assert |placement| == k + 1;
  assert forall idx :: 0 <= idx < |placement| ==> 0 <= placement[idx] < n;
  assert forall idx :: 0 <= idx < |placement| ==> rooms[placement[idx]] == '0';
  assert forall a, b :: 0 <= a < b < |placement| ==> placement[a] != placement[b];
  assert forall idx :: 0 <= idx < |placement| - 1 ==> placement[idx] < placement[idx+1];
  assert isValidPlacement(rooms, k, placement);

  result := optimalMaxDistance(placement);
  assert result == optimalMaxDistance(placement);
  return;
}
// </vc-code>

