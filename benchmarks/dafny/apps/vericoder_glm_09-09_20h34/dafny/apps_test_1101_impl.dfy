predicate isValidPlacement(rooms: string, k: int, placement: seq<int>)
{
    |placement| == k + 1 &&
    (forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|) &&
    (forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0') &&
    (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
    (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
}

// <vc-helpers>
function Min(s: set<int>): int
    requires s != {}
    ensures Min(s) in s
    ensures forall i :: i in s ==> Min(s) <= i
{
    var min := choose i | i in s;
    if exists i :: i in s && i < min then
        Min(set i | i in s && i < min)
    else
        min
}

function method generatePlacements(zeroIndices: set<int>, m: int): seq<seq<int>>
    requires m > 0
    ensures forall placement :: placement in generatePlacements(zeroIndices, m) <==> 
        |placement| == m && 
        (forall i :: 0 <= i < |placement| ==> placement[i] in zeroIndices) &&
        (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
        (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
    decreases |zeroIndices|, m
{
    if m == 1 then [seq i | i in zeroIndices]
    else if zeroIndices == {} then []
    else
        var min := Min(zeroIndices);
        var smallerCombos := generatePlacements(zeroIndices - {min}, m);
        var withMin := generatePlacements(zeroIndices - {min}, m-1);
        var withMinPrepended := [seq min + sc[i] | sc in withMin, i := 0..|sc|];
        smallerCombos + withMinPrepended
}

lemma lemma_MinIsCorrect(s: set<int>)
    requires s != {}
    ensures Min(s) in s
    ensures forall i :: i in s ==> Min(s) <= i
{
    var min := Min(s);
    if exists i :: i in s && i < min {
        lemma_MinIsCorrect(set i | i in s && i < min);
    }
}

function method findOptimalDistance(rooms: string, k: int): int
    
ghost method lemma_achievesOptimal(rooms: string, k: int)
    requires k > 0
    requires |rooms| > k
    requires |set i | 0 <= i < |rooms| && rooms[i] == '0'| >= k + 1
    
function optimalMaxDistance(placement: seq<int>): int
    requires |placement| > 0
    requires forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|
    requires forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]
    requires forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
{
    if |placement| == 1 then 0
    else
        var d := optimalMaxDistance(placement[1..]);
        if d > placement[1] - placement[0] then d else placement[1] - placement[0]
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
    return 0;
}
// </vc-code>

