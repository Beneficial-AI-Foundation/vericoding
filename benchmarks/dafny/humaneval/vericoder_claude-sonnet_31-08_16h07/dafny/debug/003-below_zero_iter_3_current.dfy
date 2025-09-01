function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
lemma psum_prefix_property(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    ensures psum(s[..i]) == if i == 0 then 0 else psum(s[..i-1]) + s[i-1]
{
    if i == 0 {
        assert s[..i] == [];
    } else {
        assert s[..i] == s[..i-1] + [s[i-1]];
        assert |s[..i]| == i;
        assert s[..i][..(|s[..i]|-1)] == s[..i-1];
        assert s[..i][|s[..i]|-1] == s[i-1];
    }
}

lemma psum_incremental(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures psum(s[..i+1]) == psum(s[..i]) + s[i]
{
    psum_prefix_property(s, i+1);
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)
    // post-conditions-start
    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var current_sum := 0;
    var i := 0;
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant current_sum == psum(ops[..i])
        invariant forall j :: 0 <= j <= i ==> psum(ops[..j]) >= 0
    {
        psum_incremental(ops, i);
        current_sum := current_sum + ops[i];
        i := i + 1;
        
        if current_sum < 0 {
            return true;
        }
    }
    
    return false;
}
// </vc-code>

