//ATOM
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
 requires 0 <= s <= t <= |a|
{
 if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

//IMPL MaxSegSum
/* code modified by LLM (iteration 2): Added helper lemma for Sum properties */
lemma SumProperties(a: seq<int>, s: int, t: int)
    requires 0 <= s <= t <= |a|
    ensures Sum(a, s, s) == 0
    ensures s < t ==> Sum(a, s, t) == Sum(a, s, t-1) + a[t-1]
{
    // Properties follow from definition
}

method MaxSegSum(a: seq<int>) returns (k: int, m: int)
 ensures 0 <= k <= m <= |a|
 ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
    if |a| == 0 {
        k, m := 0, 0;
        return;
    }
    
    k, m := 0, 0;
    var maxSum := 0;
    
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant 0 <= k <= m <= |a|
        /* code modified by LLM (iteration 2): Fixed invariant to properly cover processed segments */
        invariant forall p,q :: 0 <= p < i && p <= q <= |a| ==> Sum(a, p, q) <= maxSum
        /* code modified by LLM (iteration 2): Added invariant for segments starting at or after i */
        invariant forall p :: 0 <= p <= i ==> Sum(a, p, p) <= maxSum
        invariant maxSum == Sum(a, k, m)
    {
        var j := i;
        var currentSum := 0;
        
        while j < |a|
            invariant i <= j <= |a|
            invariant currentSum == Sum(a, i, j)
            invariant 0 <= k <= m <= |a|
            /* code modified by LLM (iteration 2): Maintained invariant for previously processed segments */
            invariant forall p,q :: 0 <= p < i && p <= q <= |a| ==> Sum(a, p, q) <= maxSum
            /* code modified by LLM (iteration 2): Added invariant for current row being processed */
            invariant forall q :: i <= q <= j ==> Sum(a, i, q) <= maxSum
            /* code modified by LLM (iteration 2): Added invariant for empty segments */
            invariant forall p :: 0 <= p <= i ==> Sum(a, p, p) <= maxSum
            invariant maxSum == Sum(a, k, m)
        {
            currentSum := currentSum + a[j];
            
            if currentSum > maxSum {
                k, m := i, j + 1;
                maxSum := currentSum;
            }
            
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 2): Added assertion to establish all segments from i have been processed */
        assert forall q :: i <= q <= |a| ==> Sum(a, i, q) <= maxSum;
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 2): Added final assertions to help prove postcondition */
    assert forall p,q :: 0 <= p < |a| && p <= q <= |a| ==> Sum(a, p, q) <= maxSum;
    /* code modified by LLM (iteration 2): Handle the case where p == |a| */
    assert forall q :: |a| <= q <= |a| ==> Sum(a, |a|, q) <= maxSum;
    /* code modified by LLM (iteration 2): Combine both cases */
    assert forall p,q :: 0 <= p <= |a| && p <= q <= |a| ==> Sum(a, p, q) <= maxSum;
}