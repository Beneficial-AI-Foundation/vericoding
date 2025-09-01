function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
lemma psumLemma(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    ensures psum(s[..i]) == if i == 0 then 0 else psum(s[..i-1]) + s[i-1]
{
    if i == 0 {
        assert s[..0] == [];
    } else {
        assert s[..i] == s[..i-1] + [s[i-1]];
    }
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
    var sum := 0;
    var i := 0;
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant sum == psum(ops[..i])
        invariant forall j :: 0 <= j <= i ==> psum(ops[..j]) >= 0
    {
        sum := sum + ops[i];
        i := i + 1;
        psumLemma(ops, i);
        
        if sum < 0 {
            return false;
        }
    }
    
    return true;
}
// </vc-code>

