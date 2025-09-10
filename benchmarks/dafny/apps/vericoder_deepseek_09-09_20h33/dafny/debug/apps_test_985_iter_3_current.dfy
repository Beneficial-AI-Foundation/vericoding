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
lemma CountAttackingPairsAdditive(positions: seq<(int, int)>, diag: int) returns (count: int)
    requires ValidInput(positions)
    requires diag >= 2 && diag <= 2000
    ensures count == |set i | 0 <= i < |positions| && positions[i].0 + positions[i].1 == diag :: i|
{
    count := 0;
    var index := 0;
    while index < |positions|
        invariant 0 <= index <= |positions|
        invariant count == |set i | 0 <= i < index && positions[i].0 + positions[i].1 == diag :: i|
    {
        if positions[index].0 + positions[index].1 == diag {
            count := count + 1;
        }
        index := index + 1;
    }
}

lemma CountAttackingPairsSubtractive(positions: seq<(int, int)>, diag: int) returns (count: int)
    requires ValidInput(positions)
    requires diag >= -999 && diag <= 999
    ensures count == |set i | 0 <= i < |positions| && positions[i].0 - positions[i].1 == diag :: i|
{
    count := 0;
    var index := 0;
    while index < |positions|
        invariant 0 <= index <= |positions|
        invariant count == |set i | 0 <= i < index && positions[i].0 - positions[i].1 == diag :: i|
    {
        if positions[index].0 - positions[index].1 == diag {
            count := count + 1;
        }
        index := index + 1;
    }
}

function Comb2(n: int): int
    requires n >= 0
{
    if n < 2 then 0 else n * (n - 1) / 2
}

ghost function Sum(start: int, end: int, f: int -> int): int
    requires start <= end
    decreases end - start
{
    if start == end then 0 else f(start) + Sum(start + 1, end, f)
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
    ghost var additiveCounts: seq<int> := [];
    ghost var subtractiveCounts: seq<int> := [];
    
    var diag := 2;
    while diag <= 2000
        invariant 2 <= diag <= 2001
        invariant |additiveCounts| == diag - 2
    {
        var count := CountAttackingPairsAdditive(positions, diag);
        additiveCounts := additiveCounts + [count];
        diag := diag + 1;
    }
    
    diag := -999;
    while diag <= 999
        invariant -999 <= diag <= 1000
        invariant |subtractiveCounts| == diag + 999
    {
        var count := CountAttackingPairsSubtractive(positions, diag);
        subtractiveCounts := subtractiveCounts + [count];
        diag := diag + 1;
    }
    
    result := 0;
    
    var i := 0;
    while i < |additiveCounts|
        invariant 0 <= i <= |additiveCounts|
        invariant result == Sum(0, i, j => Comb2(additiveCounts[j]))
    {
        result := result + Comb2(additiveCounts[i]);
        i := i + 1;
    }
    
    var old_result := result;
    i := 0;
    while i < |subtractiveCounts|
        invariant 0 <= i <= |subtractiveCounts|
        invariant result == old_result + Sum(0, i, j => Comb2(subtractiveCounts[j]))
    {
        result := result + Comb2(subtractiveCounts[i]);
        i := i + 1;
    }
}
// </vc-code>

