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

function optimalMaxDistance(placement: seq<int>) : int
  requires 1 < |placement|
  requires forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
{
  var det := placement[1] - placement[0];
  if |placement| == 2 then
    det
  else
    if det < optimalMaxDistance(placement[1..]) then
      det
    else
      optimalMaxDistance(placement[1..])
}

function getPositions(rooms: string) : seq<int>
  requires |rooms| > 0
  requires forall i :: 0 <= i < |rooms| ==> rooms[i] == '0' || rooms[i] == '1'
{
  if |rooms| == 0 then [] else 
  if rooms[0] == '0' then [0] + getPositions(rooms[1..]) 
  else getPositions(rooms[1..])
}

function maxPlace(pos: seq<int>, D: int, prev: int) : int
  requires sorted(pos)
{
  if |pos| == 0 then 0
  else if pos[0] >= prev + D then 1 + maxPlace(pos[1..], D, pos[0])
  else maxPlace(pos[1..], D, prev)
}

predicate canPlaceForD(positions: seq<int>, k: int, D: int) : bool
  requires k > 0
  requires sorted(positions)
  requires forall i :: 0 <= i < |positions| - 1 ==> positions[i] < positions[i+1]
{
  maxPlace(positions, D, -D) >= k + 1
}

method checkPlacementExists(rooms: string, k: int, D: int) returns (b: bool)
  requires k > 0
  requires |rooms| > 0
  requires forall i :: 0 <= i < |rooms| ==> rooms[i] == '0' || rooms[i] == '1'
  requires D >= 0
  ensures b == canPlaceForD(getPositions(rooms), k, D)
{
  var positions := getPositions(rooms);
  var i := 0;
  var count := 0;
  var prev := -D;
  while i < |positions| && count < k + 1
    invariant 0 <= i <= |positions|
    invariant 0 <= count <= k
    invariant prev >= -D
    invariant count == 0 || prev >= 0
  {
    if positions[i] >= prev + D {
      prev := positions[i];
      count := count + 1;
    }
    i := i + 1;
  }
  b := count == k + 1;
}

predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

lemma {:induction sorted} PosSorted(rooms: string)
  requires |rooms| > 0
  requires forall i :: 0 <= i < |rooms| ==> rooms[i] == '0' || rooms[i] == '1'
  ensures sorted(getPositions(rooms))
{
  // proof by induction on rooms
}

lemma AdequatePositions(rooms: string, k: int)
  requires |rooms| > 0
  requires k > 0
  requires forall i :: 0 <= i < |rooms| ==> rooms[i] == '0' || rooms[i] == '1'
  requires |getPositions(rooms)| >= k + 1
  ensures canPlaceForD(getPositions(rooms), k, 0)
{
  // trivial
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
  var positions := getPositions(rooms);
  // Binary search for the maximum D
  var low := 0;
  var high := n;
  while low < high
    invariant 0 <= low <= high <= n
    invariant canPlaceForD(positions, k, low)
    invariant !canPlaceForD(positions, k, high) || (high == n && canPlaceForD(positions, k, high))
  {
    var mid := (low + high + 1) / 2;
    var b := checkPlacementExists(rooms, k, mid);
    if b {
      low := mid;
    } else {
      high := mid - 1;
    }
  }
  result := low;
}
// </vc-code>

