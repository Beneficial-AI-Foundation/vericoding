predicate isValidPlacement(rooms: string, k: int, placement: seq<int>)
{
    |placement| == k + 1 &&
    (forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|) &&
    (forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0') &&
    (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
    (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
}

// <vc-helpers>
predicate isValidPlacement(rooms: string, k: int, placement: seq<int>)
{
    |placement| == k + 1 &&
    (forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|) &&
    (forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0') &&
    (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
    (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
}

function optimalMaxDistance(placement: seq<int>): int
  requires |placement| >= 2
{
  var max := 0;
  var idx := 1;
  while idx < |placement|
    invariant 1 <= idx <= |placement|
    invariant max == (if idx >= 2 then maxD(placement[0..idx]) else 0)
  {
    if placement[idx] - placement[idx-1] > max {
      max := placement[idx] - placement[idx-1];
    }
    idx := idx + 1;
  }
  max
}

function maxD(placement: seq<int>): int
  requires |placement| >= 2
{
  if |placement| == 2 then
    placement[1] - placement[0]
  else
    var maxRest := maxD(placement[1..]);
    if placement[1] - placement[0] > maxRest then
      placement[1] - placement[0]
    else
      maxRest
}

lemma AllZerosGetAssigned(rooms: string, k: int, placement: seq<int>)
  requires isValidPlacement(rooms, k, placement)
  ensures |placement| == k + 1
{
}

lemma PlacementIsSortedAndDistinct(rooms: string, k: int, placement: seq<int>)
  requires isValidPlacement(rooms, k, placement)
  ensures forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
  ensures forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]
{
}

lemma PlacementValidPositions(rooms: string, k: int, placement: seq<int>)
  requires isValidPlacement(rooms, k, placement)
  ensures forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms| && rooms[placement[i]] == '0'
{
}

lemma ZerosSequenceProperties(zeros: seq<int>, n: int, rooms: string)
  requires |zeros| == |set j | 0 <= j < n && rooms[j] == '0'|
  requires forall x :: x in zeros ==> 0 <= x < n && rooms[x] == '0'
  requires forall x :: 0 <= x < n && rooms[x] == '0' ==> x in zeros
  ensures forall i :: 0 <= i < |zeros| - 1 ==> zeros[i] < zeros[i+1]
{
}

lemma SliceIsValidPlacement(rooms: string, k: int, zeros: seq<int>, left: int)
  requires 0 <= left <= |zeros| - k - 1
  requires forall i :: 0 <= i < |zeros| - 1 ==> zeros[i] < zeros[i+1]
  requires forall i :: 0 <= i < |zeros| ==> rooms[zeros[i]] == '0'
  ensures isValidPlacement(rooms, k, zeros[left..left + k + 1])
{
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
  var zeros : seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall x :: x in zeros ==> 0 <= x < i && rooms[x] == '0'
    invariant forall x :: 0 <= x < i && rooms[x] == '0' ==> x in zeros
    invariant |zeros| == |set j | 0 <= j < i && rooms[j] == '0'|
    invariant forall idx :: 0 <= idx < |zeros| - 1 ==> zeros[idx] < zeros[idx+1]
  {
    if rooms[i] == '0' {
      zeros := zeros + [i];
    }
    i := i + 1;
  }
  
  var left := 0;
  var right := k;
  var minMaxDist := n;
  
  while right < |zeros|
    invariant 0 <= left <= |zeros| - k
    invariant k <= right <= |zeros|
    invariant left + k == right
    invariant minMaxDist >= 0
  {
    var placement := zeros[left..left + k + 1];
    ZerosSequenceProperties(zeros, n, rooms);
    SliceIsValidPlacement(rooms, k, zeros, left);
    assert isValidPlacement(rooms, k, placement);
    var maxDist := optimalMaxDistance(placement);
    if maxDist < minMaxDist {
      minMaxDist := maxDist;
    }
    left := left + 1;
    right := right + 1;
  }
  
  result := minMaxDist;
}
// </vc-code>

