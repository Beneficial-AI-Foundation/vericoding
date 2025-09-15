

// <vc-helpers>
lemma SetComprehensionProperty(s: seq<int>, x: int, k: int)
    requires 0 <= k <= |s|
    ensures (set i | 0 <= i < k && s[i] == x) == 
            (set i | 0 <= i < k-1 && s[i] == x) + (if k > 0 && s[k-1] == x then {k-1} else {})
{
    if k == 0 {
        assert (set i | 0 <= i < k && s[i] == x) == {};
    } else {
        var S1 := set i | 0 <= i < k && s[i] == x;
        var S2 := set i | 0 <= i < k-1 && s[i] == x;
        if s[k-1] == x {
            assert S1 == S2 + {k-1};
        } else {
            assert S1 == S2;
        }
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
    var idx := 0;
    var indices := {};
    
    while idx < |s|
        invariant 0 <= idx <= |s|
        invariant indices == set i | 0 <= i < idx && s[i] == x
        invariant count == |indices|
    {
        if s[idx] == x {
            indices := indices + {idx};
            count := count + 1;
        }
        idx := idx + 1;
    }
    
    assert indices == set i | 0 <= i < |s| && s[i] == x;
}
// </vc-code>

