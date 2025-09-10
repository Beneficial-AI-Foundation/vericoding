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
lemma CountPairsInMap(m: map<int, int>) returns (count: int)
    ensures count >= 0
    ensures count == (var keys := m.Keys; 
                      var sum := 0;
                      var keysSeq := SetToSeq(keys);
                      SumOfPairs(keysSeq, m, 0))
{
    count := 0;
    var keys := m.Keys;
    var processed: set<int> := {};
    
    while processed != keys
        invariant processed <= keys
        invariant count >= 0
    {
        var k :| k in keys - processed;
        var v := m[k];
        if v > 1 {
            count := count + (v * (v - 1)) / 2;
        }
        processed := processed + {k};
    }
}

function SetToSeq<T>(s: set<T>): seq<T>
{
    if |s| == 0 then []
    else 
        var x :| x in s;
        [x] + SetToSeq(s - {x})
}

function SumOfPairs(keys: seq<int>, m: map<int, int>, i: int): int
    requires 0 <= i <= |keys|
    requires forall k :: k in keys ==> k in m
    decreases |keys| - i
{
    if i == |keys| then 0
    else 
        var v := m[keys[i]];
        (if v > 1 then v * (v - 1) / 2 else 0) + SumOfPairs(keys, m, i + 1)
}
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
    
    result := 0;
    
    var sumKeys := sumDiag.Keys;
    while sumKeys != {}
        invariant result >= 0
    {
        var k :| k in sumKeys;
        var count := sumDiag[k];
        if count > 1 {
            result := result + (count * (count - 1)) / 2;
        }
        sumKeys := sumKeys - {k};
    }
    
    var diffKeys := diffDiag.Keys;
    while diffKeys != {}
        invariant result >= 0
    {
        var k :| k in diffKeys;
        var count := diffDiag[k];
        if count > 1 {
            result := result + (count * (count - 1)) / 2;
        }
        diffKeys := diffKeys - {k};
    }
}
// </vc-code>

