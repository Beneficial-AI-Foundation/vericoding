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
    requires |placement| >= 2
    requires forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
{
    if |placement| <= 1 then 0
    else
        var distances := seq(|placement| - 1, i requires 0 <= i < |placement| - 1 => placement[i+1] - placement[i]);
        minSeq(distances)
}

function minSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else
        var rest_min := minSeq(s[1..]);
        if s[0] <= rest_min then s[0] else rest_min
}

function canPlaceWithDistance(rooms: string, k: int, minDist: int): bool
    requires minDist >= 1
{
    var count := placeGreedy(rooms, k + 1, minDist, 0, 0);
    count >= k + 1
}

function placeGreedy(rooms: string, needed: int, minDist: int, start: int, placed: int): int
    requires 0 <= start <= |rooms|
    requires placed >= 0
    requires minDist >= 1
    decreases |rooms| - start, needed - placed
{
    if placed >= needed then placed
    else if start >= |rooms| then placed
    else if rooms[start] == '0' then
        var nextStart := if placed == 0 then start + 1 else start + minDist;
        if nextStart <= |rooms| then
            placeGreedy(rooms, needed, minDist, nextStart, placed + 1)
        else
            placed + 1
    else
        placeGreedy(rooms, needed, minDist, start + 1, placed)
}

lemma CanPlaceImpliesValidPlacement(rooms: string, k: int, minDist: int)
    requires k > 0
    requires minDist >= 1
    requires |rooms| > 0
    requires forall i :: 0 <= i < |rooms| ==> rooms[i] == '0' || rooms[i] == '1'
    requires canPlaceWithDistance(rooms, k, minDist)
    ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) >= minDist
{
    var placement := constructPlacement(rooms, k + 1, minDist, 0, []);
    ValidPlacementProperties(rooms, k + 1, minDist, 0, [], placement);
}

function constructPlacement(rooms: string, needed: int, minDist: int, start: int, current: seq<int>): seq<int>
    requires 0 <= start <= |rooms|
    requires needed >= 0
    requires minDist >= 1
    requires forall i :: 0 <= i < |current| ==> 0 <= current[i] < |rooms|
    requires forall i :: 0 <= i < |current| ==> rooms[current[i]] == '0'
    requires forall i, j :: 0 <= i < j < |current| ==> current[i] < current[j]
    requires forall i :: 0 <= i < |current| - 1 ==> current[i+1] - current[i] >= minDist
    decreases |rooms| - start, needed
{
    if needed == 0 then current
    else if start >= |rooms| then current
    else if rooms[start] == '0' then
        var nextStart := if |current| == 0 then start + 1 else start + minDist;
        if nextStart <= |rooms| then
            constructPlacement(rooms, needed - 1, minDist, nextStart, current + [start])
        else
            current + [start]
    else
        constructPlacement(rooms, needed, minDist, start + 1, current)
}

lemma ValidPlacementProperties(rooms: string, needed: int, minDist: int, start: int, current: seq<int>, placement: seq<int>)
    requires 0 <= start <= |rooms|
    requires needed >= 0
    requires minDist >= 1
    requires forall i :: 0 <= i < |current| ==> 0 <= current[i] < |rooms|
    requires forall i :: 0 <= i < |current| ==> rooms[current[i]] == '0'
    requires forall i, j :: 0 <= i < j < |current| ==> current[i] < current[j]
    requires forall i :: 0 <= i < |current| - 1 ==> current[i+1] - current[i] >= minDist
    requires placement == constructPlacement(rooms, needed, minDist, start, current)
    ensures forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|
    ensures forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0'
    ensures forall i, j :: 0 <= i < j < |placement| ==> placement[i] < placement[j]
    ensures forall i :: 0 <= i < |placement| - 1 ==> placement[i+1] - placement[i] >= minDist
    decreases |rooms| - start, needed
{
    if needed == 0 {
    } else if start >= |rooms| {
    } else if rooms[start] == '0' {
        var nextStart := if |current| == 0 then start + 1 else start + minDist;
        if nextStart <= |rooms| {
            ValidPlacementProperties(rooms, needed - 1, minDist, nextStart, current + [start], placement);
        }
    } else {
        ValidPlacementProperties(rooms, needed, minDist, start + 1, current, placement);
    }
}

lemma InitialPlacementExists(rooms: string, k: int)
    requires k > 0
    requires |rooms| > 0
    requires |set i | 0 <= i < |rooms| && rooms[i] == '0'| >= k + 1
    ensures exists placement :: isValidPlacement(rooms, k, placement)
{
    var placement := constructPlacement(rooms, k + 1, 1, 0, []);
    ValidPlacementProperties(rooms, k + 1, 1, 0, [], placement);
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
    var left := 1;
    var right := n;
    var maxMinDist := 1;
    
    InitialPlacementExists(rooms, k);
    
    while left <= right
        invariant 1 <= left <= right + 1 <= n + 1
        invariant maxMinDist >= 1
        invariant exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) >= maxMinDist
    {
        var mid := (left + right) / 2;
        
        if canPlaceWithDistance(rooms, k, mid) {
            maxMinDist := mid;
            left := mid + 1;
            CanPlaceImpliesValidPlacement(rooms, k, mid);
        } else {
            right := mid - 1;
        }
    }
    
    result := maxMinDist;
    
    var finalPlacement := constructPlacement(rooms, k + 1, maxMinDist, 0, []);
    ValidPlacementProperties(rooms, k + 1, maxMinDist, 0, [], finalPlacement);
    assert isValidPlacement(rooms, k, finalPlacement);
    assert optimalMaxDistance(finalPlacement) >= maxMinDist;
}
// </vc-code>

