function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
function psum_helper(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum_helper(s[..(|s|)-1]) + s[ |s| - 1 ]
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
    for i := 0 to |ops|
        invariant 0 <= i <= |ops|
        invariant current_sum == psum_helper(ops[..i])        
        invariant forall k :: 0 <= k < i ==> psum_helper(ops[..k]) >= 0
    {
        if current_sum < 0 {
            return false;
        }
        if i < |ops| {
            current_sum := current_sum + ops[i];
        } else {
          assert current_sum >= 0; 
        }
    }
    return true;
}
// </vc-code>

