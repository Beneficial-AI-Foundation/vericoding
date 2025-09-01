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
    // The prefix sum up to an empty sequence is 0.
    // The loop iterates from i = 0 up to |ops|,
    // where `i` represents the effective length of the prefix.
    // For i=0, the prefix is ops[..0], which is an empty sequence.
    // The sum of an empty sequence is 0.
    // So current_sum represents `psum(ops[..i])` where `i` is the current effective prefix length.
    // For any i, `current_sum` always holds `psum(ops[..i])`.
    for i := 0 to |ops|
        invariant 0 <= i <= |ops|
        // If we assumed `res` is true, then for all `k` such that `0 <= k < i`, `psum(ops[..k])` must be non-negative.
        invariant forall k :: 0 <= k < i ==> psum_helper(ops[..k]) >= 0
        // `current_sum` always represents the prefix sum `psum(ops[..i])`.
        invariant current_sum == psum_helper(ops[..i])
    {
        // If current_sum ever goes below zero, this means
        // `psum(ops[..i])` is negative. We can then return `false`.
        if current_sum < 0 {
            return false;
        }

        // We are processing the prefix up to `i`.
        // The next iteration will represent prefix sum up to `i+1`.
        // So we add `ops[i]` to `current_sum` before advancing `i`.
        if i < |ops| {
            current_sum := current_sum + ops[i];
        }
    }
    // If the loop completes, it means `current_sum` (which represents `psum(ops[..i])`)
    // was never negative for any i from 0 to |ops|.
    // Therefore, we can return `true`.
    return true;
}
// </vc-code>

