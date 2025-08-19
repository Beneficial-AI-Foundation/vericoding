//ATOM
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
 requires 0 <= s <= t <= |a|
{
 if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

//IMPL SPEC
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
 ensures 0 <= k <= m <= |a|
 ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
    k := 0;
    m := 0;
    var maxSum := Sum(a, 0, 0);
    
    var i := 0;
    while i <= |a|
        invariant 0 <= i <= |a| + 1
        invariant 0 <= k <= m <= |a|
        invariant maxSum == Sum(a, k, m)
        invariant forall p,q :: 0 <= p <= q <= |a| && (p < i || (p == i && q == i)) ==> Sum(a, p, q) <= maxSum
    {
        var j := i;
        while j <= |a|
            invariant i <= j <= |a| + 1
            invariant 0 <= k <= m <= |a|
            invariant maxSum == Sum(a, k, m)
            invariant forall p,q :: 0 <= p <= q <= |a| && (p < i || (p == i && q < j)) ==> Sum(a, p, q) <= maxSum
        {
            var currentSum := Sum(a, i, j);
            if currentSum > maxSum {
                k := i;
                m := j;
                maxSum := currentSum;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}