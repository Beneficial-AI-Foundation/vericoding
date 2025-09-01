

// <vc-helpers>
lemma CountEqualsSetSize(s: seq<int>, x: int, count: int)
    requires count == |multiset(i | 0 <= i < |s| && s[i] == x :: i)|
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
{
    var indices := set i | 0 <= i < |s| && s[i] == x;
    var multiIndices := multiset(i | 0 <= i < |s| && s[i] == x :: i);
    
    assert forall i :: i in indices <==> (0 <= i < |s| && s[i] == x);
    assert forall i :: i in multiIndices <==> (0 <= i < |s| && s[i] == x);
    
    SetMultisetEquality(indices, multiIndices);
}

lemma SetMultisetEquality<T>(s: set<T>, ms: multiset<T>)
    requires forall x :: x in s <==> x in ms
    requires forall x :: x in ms ==> ms[x] == 1
    ensures |s| == |ms|
{
}
// </vc-helpers>

// <vc-spec>
method freq(s: seq<int>, x: int) returns (count: int)
    // post-conditions-start
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == |(set j | 0 <= j < i && s[j] == x)|
    {
        if s[i] == x {
            count := count + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

