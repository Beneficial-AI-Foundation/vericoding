function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>

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
        invariant i <= |ops|
        invariant sum == psum(ops[..i])
        invariant sum >= 0
    {
        sum := sum + ops[i];
        if sum < 0 {
            return false;
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>

