

// <vc-helpers>
lemma CountEqualsSetSize(s: seq<int>, x: int, count: int)
    requires count == |set i | 0 <= i < |s| && s[i] == x|
    ensures count == |(set i | 0 <= i < |s| && s[i] == x)|
{
}

lemma SetSizeIncrement(s: seq<int>, x: int, i: int)
    requires 0 <= i < |s|
    ensures s[i] == x ==> |(set j | 0 <= j < i+1 && s[j] == x)| == |(set j | 0 <= j < i && s[j] == x)| + 1
    ensures s[i] != x ==> |(set j | 0 <= j < i+1 && s[j] == x)| == |(set j | 0 <= j < i && s[j] == x)|
{
    var oldSet := set j | 0 <= j < i && s[j] == x;
    var newSet := set j | 0 <= j < i+1 && s[j] == x;
    
    if s[i] == x {
        assert newSet == oldSet + {i};
        assert i !in oldSet;
    } else {
        assert newSet == oldSet;
    }
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
            SetSizeIncrement(s, x, i);
            count := count + 1;
        } else {
            SetSizeIncrement(s, x, i);
        }
        i := i + 1;
    }
}
// </vc-code>

