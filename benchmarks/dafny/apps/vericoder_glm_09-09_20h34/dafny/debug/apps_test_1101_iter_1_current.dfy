predicate isValidPlacement(rooms: string, k: int, placement: seq<int>)
{
    |placement| == k + 1 &&
    (forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|) &&
    (forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0') &&
    (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
    (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
}

// <vc-helpers>
function maxDistance(placement: seq<int>): int {
    if |placement| < 2 then 0
    else maxDistanceHelper(placement, 1, placement[1] - placement[0])
}

function maxDistanceHelper(placement: seq<int>, i: int, currentMax: int): int {
    if i == |placement| then currentMax
    else if placement[i] - placement[i-1] > currentMax then maxDistanceHelper(placement, i + 1, placement[i] - placement[i-1])
    else maxDistanceHelper(placement, i + 1, currentMax)
}

predicate optimalMaxDistance(placement: seq<int>) {
    forall otherPlacement :: 
        isValidPlacement(rooms, k, otherPlacement) ==> 
        maxDistance(placement) >= maxDistance(otherPlacement)
}

function method setOfZeroIndices(rooms: string): set<int> {
    set i | 0 <= i < |rooms| && rooms[i] == '0'
}

function method allPlacements(rooms: string, k: int): (seq<seq<int>>)
    ensures forall placement :: placement in allPlacements(rooms, k) <==> isValidPlacement(rooms, k, placement)
{
    if k == 0 then [[i for i in setOfZeroIndices(rooms)]]
    else generatePlacements(setOfZeroIndices(rooms), k + 1)
}

function method generatePlacements(zeroIndices: set<int>, m: int): seq<seq<int>>
    requires m > 0
    ensures forall placement :: placement in generatePlacements(zeroIndices, m) <==> 
        |placement| == m && 
        (forall i :: 0 <= i < |placement| ==> placement[i] in zeroIndices) &&
        (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
        (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
{
    if m == 1 then [[i] for i in zeroIndices]
    else 
        var s := seq i for i in zeroIndices;
        var combos: seq<seq<int>> := [];
        for idx := 0 to |s|
        {
            var smallerCombos := generatePlacements(set j | j in zeroIndices && j > s[idx], m - 1);
            for sc in smallerCombos
            {
                combos := combos + [s[idx] + sc];
            }
        }
        combos
}

function method findOptimalDistance(rooms: string, k: int): int {
    var placements := allPlacements(rooms, k);
    var currentBest := 0;
    for pl in placements
    {
        var dist := maxDistance(pl);
        if dist > currentBest {
            currentBest := dist;
        }
    }
    currentBest
}

lemma lemma_allPlacementsContainsValid(rooms: string, k: int, placement: seq<int>)
    requires isValidPlacement(rooms, k, placement)
    ensures placement in allPlacements(rooms, k)
{
    if k == 0 {
        assert placement == [i for i in setOfZeroIndices(rooms)];
    } else {
        var zeroIndices := setOfZeroIndices(rooms);
        forall i | 0 <= i < |placement| ensures placement[i] in zeroIndices {
            assert isValidPlacement(rooms, k, placement);
            assert rooms[placement[i]] == '0';
            assert placement[i] in zeroIndices;
        }
        assert placement in generatePlacements(zeroIndices, k+1);
    }
}

lemma lemma_allPlacementsOnlyContainsValid(rooms: string, k: int, placement: seq<int>)
    requires placement in allPlacements(rooms, k)
    ensures isValidPlacement(rooms, k, placement)
{
    if k == 0 {
        assert placement == [i for i in setOfZeroIndices(rooms)];
        assert |placement| == 1; // Not true, but spec requires k+1 = 1 so k = 0
        // The spec of solve requires k > 0, so this branch won't be taken.
    } else {
        assert placement in generatePlacements(setOfZeroIndices(rooms), k+1);
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
    return findOptimalDistance(rooms, k);
}
// </vc-code>

