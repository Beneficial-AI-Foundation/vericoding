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
    var rec := optimalMaxDistance(placement[1..]);
    if det > rec then det else rec
}

function canPlaceWithMinDist(d: int, rooms: string, k: int) : bool
{
  var count := 0;
  var pos := -d - 1;
  var i := 0;
  while i < |rooms| && count < k + 1
  {
    if rooms[i] == '0' then
      if i - pos >= d then
      {
        pos := i;
        count := count + 1;
      }
    i := i + 1;
  }
  count == k + 1
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
  var low := 0;
  var high := |rooms| - 1;
  while low < high
  {
    var mid := (low + high + 1) / 2;
    if canPlaceWithMinDist(mid, rooms, k) then
      low := mid;
    else
      high := mid - 1;
  }
  result := low;
}
// </vc-code>

