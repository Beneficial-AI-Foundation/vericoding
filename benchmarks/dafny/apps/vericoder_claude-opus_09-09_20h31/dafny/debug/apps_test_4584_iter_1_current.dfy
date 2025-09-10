predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

// <vc-helpers>
lemma SubordinateCountDefinition(aa: seq<int>, boss_id: int, count: int)
    ensures SubordinateCount(aa, boss_id) == count <==> 
            |set j | 0 <= j < |aa| && aa[j] == boss_id| == count
{
}

lemma SubordinateCountBounds(aa: seq<int>, boss_id: int)
    ensures 0 <= SubordinateCount(aa, boss_id) <= |aa|
{
    var s := set j | 0 <= j < |aa| && aa[j] == boss_id;
    assert s <= set j | 0 <= j < |aa|;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
        invariant forall j :: 0 <= j < i ==> result[j] == SubordinateCount(aa, j + 1)
    {
        var count := 0;
        var k := 0;
        
        while k < |aa|
            invariant 0 <= k <= |aa|
            invariant count == |set j | 0 <= j < k && aa[j] == i + 1|
        {
            if aa[k] == i + 1 {
                count := count + 1;
            }
            k := k + 1;
        }
        
        assert count == |set j | 0 <= j < |aa| && aa[j] == i + 1|;
        assert count == SubordinateCount(aa, i + 1);
        
        result := result + [count];
        i := i + 1;
    }
}
// </vc-code>

