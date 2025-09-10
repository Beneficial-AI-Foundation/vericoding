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
    if |placement| <= 1 then 0
    else
        var distances := seq(|placement| - 1, i requires 0 <= i < |placement| - 1 => placement[i+1] - placement[i]);
        minOfSeq(distances)
}

function minOfSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else 
        var rest := minOfSeq(s[1..]);
        if s[0] < rest then s[0] else rest
}

predicate canPlaceWithMinDistance(rooms: string, k: int, minDist: int) 
    requires |rooms| > 0
    requires k >= 0
{
    exists placement :: isValidPlacement(rooms, k, placement) && 
        forall i :: 0 <= i < |placement| - 1 ==> placement[i+1] - placement[i] >= minDist
}

method findAvailableRooms(rooms: string) returns (available: seq<int>)
    requires |rooms| > 0
    ensures forall i :: 0 <= i < |available| ==> 0 <= available[i] < |rooms| && rooms[available[i]] == '0'
    ensures forall i :: 0 <= i < |available| - 1 ==> available[i] < available[i+1]
    ensures |available| == |set i | 0 <= i < |rooms| && rooms[i] == '0'|
{
    available := [];
    var i := 0;
    while i < |rooms|
        invariant 0 <= i <= |rooms|
        invariant forall j :: 0 <= j < |available| ==> 0 <= available[j] < i && rooms[available[j]] == '0'
        invariant forall j :: 0 <= j < |available| - 1 ==> available[j] < available[j+1]
        invariant |available| == |set j | 0 <= j < i && rooms[j] == '0'|
    {
        if rooms[i] == '0' {
            available := available + [i];
        }
        i := i + 1;
    }
}

method checkPlacement(available: seq<int>, k: int, minDist: int) returns (canPlace: bool, placement: seq<int>)
    requires |available| > k >= 0
    requires forall i :: 0 <= i < |available| - 1 ==> available[i] < available[i+1]
    ensures canPlace ==> |placement| == k + 1
    ensures canPlace ==> forall i :: 0 <= i < |placement| ==> placement[i] in available
    ensures canPlace ==> forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
    ensures canPlace ==> forall i :: 0 <= i < |placement| - 1 ==> placement[i+1] - placement[i] >= minDist
{
    placement := [available[0]];
    var lastPos := available[0];
    var i := 1;
    
    while i < |available| && |placement| <= k
        invariant 1 <= i <= |available|
        invariant 1 <= |placement| <= k + 1
        invariant forall j :: 0 <= j < |placement| ==> placement[j] in available[..i]
        invariant forall j :: 0 <= j < |placement| - 1 ==> placement[j] < placement[j+1]
        invariant forall j :: 0 <= j < |placement| - 1 ==> placement[j+1] - placement[j] >= minDist
        invariant |placement| > 0 && lastPos == placement[|placement| - 1]
    {
        if available[i] - lastPos >= minDist {
            placement := placement + [available[i]];
            lastPos := available[i];
        }
        i := i + 1;
    }
    
    canPlace := |placement| == k + 1;
}

method computeMinDistance(placement: seq<int>) returns (minDist: int)
    requires |placement| > 1
    requires forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
    ensures minDist == optimalMaxDistance(placement)
{
    minDist := placement[1] - placement[0];
    var i := 2;
    while i < |placement|
        invariant 2 <= i <= |placement|
        invariant minDist > 0
        invariant forall j :: 0 <= j < i - 1 ==> minDist <= placement[j+1] - placement[j]
    {
        var dist := placement[i] - placement[i-1];
        if dist < minDist {
            minDist := dist;
        }
        i := i + 1;
    }
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
    var available := findAvailableRooms(rooms);
    
    if |available| == k + 1 {
        var minDist := computeMinDistance(available);
        return minDist;
    }
    
    var left := 1;
    var right := n;
    var bestDist := 0;
    var bestPlacement := available[..k+1];
    
    while left <= right
        invariant 0 <= left <= n + 1
        invariant 0 <= right <= n
        invariant 0 <= bestDist < left
        invariant |bestPlacement| == k + 1
        invariant forall i :: 0 <= i < |bestPlacement| ==> bestPlacement[i] in available
        invariant forall i :: 0 <= i < |bestPlacement| - 1 ==> bestPlacement[i] < bestPlacement[i+1]
        invariant forall i :: 0 <= i < |bestPlacement| - 1 ==> bestPlacement[i+1] - bestPlacement[i] >= bestDist
    {
        var mid := (left + right) / 2;
        var canPlace, placement := checkPlacement(available, k, mid);
        
        if canPlace {
            bestDist := mid;
            bestPlacement := placement;
            left := mid + 1;
        } else {
            right := mid - 1;
        }
    }
    
    result := bestDist;
}
// </vc-code>

