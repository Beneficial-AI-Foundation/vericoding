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
lemma SubordinateCountBounds(aa: seq<int>, boss_id: int)
    ensures SubordinateCount(aa, boss_id) >= 0
    ensures SubordinateCount(aa, boss_id) <= |aa|
{
}

lemma SubordinateCountCorrect(aa: seq<int>, boss_id: int, count: int)
    requires count == |set j | 0 <= j < |aa| && aa[j] == boss_id|
    ensures count == SubordinateCount(aa, boss_id)
{
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
        invariant forall k :: 0 <= k < i ==> result[k] >= 0
        invariant forall k :: 0 <= k < i ==> result[k] == SubordinateCount(aa, k + 1)
    {
        var count := 0;
        var j := 0;
        while j < |aa|
            invariant 0 <= j <= |aa|
            invariant count == |set k | 0 <= k < j && aa[k] == i + 1|
        {
            if aa[j] == i + 1 {
                count := count + 1;
            }
            j := j + 1;
        }
        
        assert count == |set k | 0 <= k < |aa| && aa[k] == i + 1|;
        assert count == SubordinateCount(aa, i + 1);
        SubordinateCountBounds(aa, i + 1);
        
        result := result + [count];
        i := i + 1;
    }
}
// </vc-code>

