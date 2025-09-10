predicate ValidInput(n: int, k: int, heights: seq<int>)
{
    n >= 1 && k >= 1 && |heights| == n && 
    forall i :: 0 <= i < |heights| ==> heights[i] >= 1
}

function CountEligible(heights: seq<int>, k: int): int
{
    |set i | 0 <= i < |heights| && heights[i] >= k :: i|
}

// <vc-helpers>
lemma CountEligiblePrefix(heights: seq<int>, k: int, i: int)
    requires 0 <= i <= |heights|
    ensures CountEligible(heights[..i], k) == |set j | 0 <= j < i && heights[j] >= k :: j|
{
    assert heights[..i] == heights[0..i];
    var s1 := set j | 0 <= j < |heights[..i]| && heights[..i][j] >= k :: j;
    var s2 := set j | 0 <= j < i && heights[j] >= k :: j;
    
    assert |heights[..i]| == i;
    assert forall j :: 0 <= j < i ==> heights[..i][j] == heights[j];
    assert s1 == s2;
}

lemma CountEligibleExtend(heights: seq<int>, k: int, i: int, oldCount: int)
    requires 0 <= i < |heights|
    requires oldCount == |set j | 0 <= j < i && heights[j] >= k :: j|
    ensures heights[i] >= k ==> 
        |set j | 0 <= j <= i && heights[j] >= k :: j| == oldCount + 1
    ensures heights[i] < k ==> 
        |set j | 0 <= j <= i && heights[j] >= k :: j| == oldCount
{
    var sBefore := set j | 0 <= j < i && heights[j] >= k :: j;
    var sAfter := set j | 0 <= j <= i && heights[j] >= k :: j;
    
    if heights[i] >= k {
        assert sAfter == sBefore + {i};
        assert i !in sBefore;
        assert |sAfter| == |sBefore| + 1;
    } else {
        assert sAfter == sBefore;
    }
}

lemma SetSizeBound(heights: seq<int>, k: int, i: int)
    requires 0 <= i <= |heights|
    ensures |set j | 0 <= j < i && heights[j] >= k :: j| <= i
{
    var s := set j | 0 <= j < i && heights[j] >= k :: j;
    assert s <= set j | 0 <= j < i :: j;
    assert |set j | 0 <= j < i :: j| == i;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (count: int)
    requires ValidInput(n, k, heights)
    ensures 0 <= count <= |heights|
    ensures count == CountEligible(heights, k)
// </vc-spec>
// <vc-code>
{
    count := 0;
    var i := 0;
    
    while i < |heights|
        invariant 0 <= i <= |heights|
        invariant 0 <= count <= i
        invariant count == |set j | 0 <= j < i && heights[j] >= k :: j|
    {
        var oldCount := count;
        if heights[i] >= k {
            count := count + 1;
        }
        CountEligibleExtend(heights, k, i, oldCount);
        SetSizeBound(heights, k, i + 1);
        i := i + 1;
    }
    
    assert i == |heights|;
    assert count == |set j | 0 <= j < |heights| && heights[j] >= k :: j|;
}
// </vc-code>

