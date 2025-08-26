predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
method Insert(sorted: seq<int>, x: int) returns (result: seq<int>)
    requires IsSorted(sorted)
    ensures IsSorted(result)
    ensures multiset(result) == multiset(sorted) + multiset{x}
    ensures |result| == |sorted| + 1
{
    var i := 0;
    while i < |sorted| && sorted[i] <= x
        invariant 0 <= i <= |sorted|
        invariant forall k :: 0 <= k < i ==> sorted[k] <= x
    {
        i := i + 1;
    }
    result := sorted[..i] + [x] + sorted[i..];
    
    // Prove the multiset property
    assert sorted == sorted[..i] + sorted[i..];
    assert multiset(sorted) == multiset(sorted[..i]) + multiset(sorted[i..]);
    assert multiset(result) == multiset(sorted[..i]) + multiset([x]) + multiset(sorted[i..]);
    assert multiset(result) == multiset(sorted[..i]) + multiset(sorted[i..]) + multiset{x};
    assert multiset(result) == multiset(sorted) + multiset{x};
    
    // Prove that result is sorted
    assert forall p, q :: 0 <= p < q < i ==> result[p] <= result[q];
    assert forall p :: 0 <= p < i ==> result[p] <= x;
    assert forall q :: i + 1 <= q < |result| ==> x <= result[q];
    assert forall p, q :: i + 1 <= p < q < |result| ==> result[p] <= result[q];
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
    r := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant IsSorted(r)
        invariant multiset(r) == multiset(s[..i])
    {
        var old_r := r;
        r := Insert(r, s[i]);
        i := i + 1;
        
        // Help prove the multiset invariant
        assert multiset(r) == multiset(old_r) + multiset{s[i-1]};
        assert multiset(old_r) == multiset(s[..i-1]);
        assert s[..i] == s[..i-1] + [s[i-1]];
        assert multiset(s[..i]) == multiset(s[..i-1]) + multiset{s[i-1]};
    }
    
    // At the end, prove the postconditions
    assert i == |s|;
    assert s[..i] == s;
}
// </vc-code>