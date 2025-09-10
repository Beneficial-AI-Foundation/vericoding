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
    requires |placement| > 1
    requires forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
    ensures optimalMaxDistance(placement) >= 1
{
    var distances := seq(|placement| - 1, i requires 0 <= i < |placement| - 1 => placement[i+1] - placement[i]);
    minOfSeq(distances)
}

function minOfSeq(s: seq<int>): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures minOfSeq(s) >= 1
{
    if |s| == 1 then s[0]
    else 
        var rest := minOfSeq(s[1..]);
        if s[0] < rest then s[0] else rest
}

lemma SetCardinalityLemma(rooms: string, i: int)
    requires 0 <= i < |rooms|
    requires rooms[i] == '0'
    ensures |set j | 0 <= j <= i && rooms[j] == '0'| == |set j | 0 <= j < i && rooms[j] == '0'| + 1
{
    var S1 := set j | 0 <= j <= i && rooms[j] == '0';
    var S2 := set j | 0 <= j < i && rooms[j] == '0';
    assert S1 == S2 + {i};
    assert i !in S2;
}

method findAvailableRooms(rooms: string) returns (available: seq<int>)
    requires |rooms| > 0
    ensures forall i :: 0 <= i < |available| ==> 0 <= available[i] < |rooms| && rooms[available[i]] == '0'
    ensures forall i :: 0 <= i < |available| - 1 ==> available[i] < available[i+1]
    ensures forall i, j :: 0 <= i < j < |available| ==> available[i] != available[j]
    ensures |available| == |set i | 0 <= i < |rooms| && rooms[i] == '0'|
{
    available := [];
    var i := 0;
    ghost var seen := {};
    
    while i < |rooms|
        invariant 0 <= i <= |rooms|
        invariant forall j :: 0 <= j < |available| ==> 0 <= available[j] < i && rooms[available[j]] == '0'
        invariant forall j :: 0 <= j < |available| - 1 ==> available[j] < available[j+1]
        invariant forall j, k :: 0 <= j < k < |available| ==> available[j] != available[k]
        invariant seen == set j | 0 <= j < i && rooms[j] == '0'
        invariant |available| == |seen|
        invariant forall j :: 0 <= j < |available| ==> available[j] in seen
        invariant forall idx :: idx in seen ==> exists j :: 0 <= j < |available| && available[j] == idx
    {
        if rooms[i] == '0' {
            ghost var oldSeen := seen;
            available := available + [i];
            seen := seen + {i};
            assert i !in oldSeen;
            if |available| > 1 {
                assert available[|available|-2] < i;
            }
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
    ensures canPlace ==> forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]
    ensures canPlace ==> forall i :: 0 <= i < |placement| - 1 ==> placement[i+1] - placement[i] >= minDist
    ensures !canPlace ==> |placement| <= k
{
    placement := [available[0]];
    var lastPos := available[0];
    var i := 1;
    
    while i < |available| && |placement| <= k
        invariant 1 <= i <= |available|
        invariant 1 <= |placement| <= k + 1
        invariant forall j :: 0 <= j < |placement| ==> exists idx :: 0 <= idx < i && placement[j] == available[idx]
        invariant forall j :: 0 <= j < |placement| ==> placement[j] in available[..i]
        invariant forall j :: 0 <= j < |placement| - 1 ==> placement[j] < placement[j+1]
        invariant forall j, k :: 0 <= j < k < |placement| ==> placement[j] != placement[k]
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
    ensures minDist >= 1
    ensures minDist == optimalMaxDistance(placement)
{
    minDist := placement[1] - placement[0];
    var i := 2;
    while i < |placement|
        invariant 2 <= i <= |placement|
        invariant minDist >= 1
        invariant forall j :: 0 <= j < i - 1 ==> minDist <= placement[j+1] - placement[j]
        invariant var distances := seq(i - 1, idx requires 0 <= idx < i - 1 => placement[idx+1] - placement[idx]);
                 minDist == minOfSeq(distances)
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
        // All available positions must be used
        assert forall i :: 0 <= i < |available| ==> 0 <= available[i] < |rooms| && rooms[available[i]] == '0';
        assert forall i :: 0 <= i < |available| - 1 ==> available[i] < available[i+1];
        assert forall i, j :: 0 <= i < j < |available| ==> available[i] != available[j];
        assert isValidPlacement(rooms, k, available);
        
        var minDist := computeMinDistance(available);
        assert optimalMaxDistance(available) == minDist;
        return minDist;
    }
    
    var left := 1;
    var right := n;
    
    // Initial placement using first k+1 positions
    var canPlace0, placement0 := checkPlacement(available, k, 1);
    assert |available| > k;
    assert canPlace0;
    var bestPlacement := placement0;
    var bestDist := 1;
    
    while left <= right
        invariant 0 <= left <= n + 1
        invariant 0 <= right <= n
        invariant 1 <= bestDist
        invariant bestDist < left || left > right
        invariant |bestPlacement| == k + 1
        invariant forall i :: 0 <= i < |bestPlacement| ==> bestPlacement[i] in available
        invariant forall i :: 0 <= i < |bestPlacement| - 1 ==> bestPlacement[i] < bestPlacement[i+1]
        invariant forall i, j :: 0 <= i < j < |bestPlacement| ==> bestPlacement[i] != bestPlacement[j]
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
    
    assert forall i :: 0 <= i < |bestPlacement| ==> 0 <= bestPlacement[i] < |rooms| && rooms[bestPlacement[i]] == '0';
    assert forall i, j :: 0 <= i < j < |bestPlacement| ==> bestPlacement[i] != bestPlacement[j];
    assert isValidPlacement(rooms, k, bestPlacement);
    
    var actualMinDist := computeMinDistance(bestPlacement);
    assert actualMinDist >= bestDist;
    assert optimalMaxDistance(bestPlacement) == actualMinDist;
    
    result := actualMinDist;
}
// </vc-code>

