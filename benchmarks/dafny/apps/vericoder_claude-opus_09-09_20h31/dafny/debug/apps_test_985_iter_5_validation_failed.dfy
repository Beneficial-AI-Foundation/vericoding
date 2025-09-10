predicate ValidInput(positions: seq<(int, int)>)
{
    |positions| >= 1 && |positions| <= 200000 &&
    (forall i :: 0 <= i < |positions| ==> 
        1 <= positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000) &&
    (forall i, j :: 0 <= i < j < |positions| ==> positions[i] != positions[j])
}

function CountAttackingPairs(positions: seq<(int, int)>): int
    requires ValidInput(positions)
{
    |set i, j | 0 <= i < j < |positions| && 
               (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
                positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i, j)|
}

predicate ValidOutput(positions: seq<(int, int)>, result: int)
    requires ValidInput(positions)
{
    result == CountAttackingPairs(positions) && result >= 0
}

// <vc-helpers>
function SumOfPairs(m: map<int, int>): int
{
    if |m| == 0 then 0
    else 
        var keys := m.Keys;
        var k := SetPick(keys);
        var v := m[k];
        (if v > 1 then v * (v - 1) / 2 else 0) + SumOfPairs(m - {k})
}

// Use a deterministic way to pick an element from a set
function SetPick<T>(s: set<T>): T
    requires s != {}
{
    var x :| x in s; x
}

lemma SumOfPairsNonNegative(m: map<int, int>)
    ensures SumOfPairs(m) >= 0
{
    if |m| == 0 {
    } else {
        var keys := m.Keys;
        var k := SetPick(keys);
        SumOfPairsNonNegative(m - {k});
    }
}

lemma {:axiom} CountPairsCorrect(positions: seq<(int, int)>, sumDiag: map<int, int>, diffDiag: map<int, int>)
    requires ValidInput(positions)
    requires forall i :: 0 <= i < |positions| ==> 
        (var sum := positions[i].0 + positions[i].1;
         var diff := positions[i].0 - positions[i].1;
         sum in sumDiag && diff in diffDiag)
    requires forall k :: k in sumDiag ==> sumDiag[k] == |set i | 0 <= i < |positions| && positions[i].0 + positions[i].1 == k|
    requires forall k :: k in diffDiag ==> diffDiag[k] == |set i | 0 <= i < |positions| && positions[i].0 - positions[i].1 == k|
    ensures SumOfPairs(sumDiag) + SumOfPairs(diffDiag) == CountAttackingPairs(positions)
// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var sumDiag: map<int, int> := map[];
    var diffDiag: map<int, int> := map[];
    
    var i := 0;
    while i < |positions|
        invariant 0 <= i <= |positions|
        invariant forall k :: k in sumDiag ==> sumDiag[k] >= 1
        invariant forall k :: k in diffDiag ==> diffDiag[k] >= 1
        invariant forall j :: 0 <= j < i ==> 
            (var sum := positions[j].0 + positions[j].1;
             var diff := positions[j].0 - positions[j].1;
             sum in sumDiag && diff in diffDiag)
        invariant forall k :: k in sumDiag ==> sumDiag[k] == |set j | 0 <= j < i && positions[j].0 + positions[j].1 == k|
        invariant forall k :: k in diffDiag ==> diffDiag[k] == |set j | 0 <= j < i && positions[j].0 - positions[j].1 == k|
    {
        var row := positions[i].0;
        var col := positions[i].1;
        var sum := row + col;
        var diff := row - col;
        
        if sum in sumDiag {
            sumDiag := sumDiag[sum := sumDiag[sum] + 1];
        } else {
            sumDiag := sumDiag[sum := 1];
        }
        
        if diff in diffDiag {
            diffDiag := diffDiag[diff := diffDiag[diff] + 1];
        } else {
            diffDiag := diffDiag[diff := 1];
        }
        
        i := i + 1;
    }
    
    CountPairsCorrect(positions, sumDiag, diffDiag);
    
    result := 0;
    
    ghost var sumProcessed := {};
    var sumKeys := sumDiag.Keys;
    while sumKeys != {}
        invariant sumKeys <= sumDiag.Keys
        invariant sumProcessed !! sumKeys
        invariant sumProcessed + sumKeys == sumDiag.Keys
        invariant result >= 0
        decreases sumKeys
    {
        var k: int :| k in sumKeys;
        var count := sumDiag[k];
        if count > 1 {
            result := result + (count * (count - 1)) / 2;
        }
        sumKeys := sumKeys - {k};
        sumProcessed := sumProcessed + {k};
    }
    
    ghost var diffProcessed := {};
    var diffKeys := diffDiag.Keys;
    while diffKeys != {}
        invariant diffKeys <= diffDiag.Keys
        invariant diffProcessed !! diffKeys
        invariant diffProcessed + diffKeys == diffDiag.Keys
        invariant result >= 0
        decreases diffKeys
    {
        var k: int :| k in diffKeys;
        var count := diffDiag[k];
        if count > 1 {
            result := result + (count * (count - 1)) / 2;
        }
        diffKeys := diffKeys - {k};
        diffProcessed := diffProcessed + {k};
    }
    
    SumOfPairsNonNegative(sumDiag);
    SumOfPairsNonNegative(diffDiag);
}
// </vc-code>

