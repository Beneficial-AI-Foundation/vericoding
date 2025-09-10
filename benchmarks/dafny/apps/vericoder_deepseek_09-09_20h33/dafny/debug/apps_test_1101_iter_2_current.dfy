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
  if |placement| == 2 then
    placement[1] - placement[0]
  else
    var maxDist := optimalMaxDistance(placement[1..]);
    if placement[1] - placement[0] > maxDist then
      placement[1] - placement[0]
    else
      maxDist
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
    var maxDist := zeros[right] - zeros[left];
    if maxDist < minMaxDist {
      minMaxDist := maxDist;
    }
    left := left + 1;
    right := right + 1;
  }
  
  result := minMaxDist;
}
// </vc-code>

