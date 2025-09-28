// <vc-preamble>
/*
 * Dafny specification for Hermite polynomial series subtraction.
 * This file implements the specification for subtracting one Hermite series from another,
 * performing component-wise subtraction with missing coefficients treated as zero.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Max function takes `int` inputs and returns an `int`. */
function Max(a: int, b: int): int {
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method HermiteSub(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
    ensures |result| == if |c1| >= |c2| then |c1| else |c2|
    ensures forall i :: 0 <= i < |result| ==>
        if i < |c1| && i < |c2| then
            result[i] == c1[i] - c2[i]
        else if i < |c1| && i >= |c2| then
            result[i] == c1[i]
        else if i >= |c1| && i < |c2| then
            result[i] == -c2[i]
        else
            false  // This case should never occur given the length constraint
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed compilation error where `new seq<real>` was used. Sequences are initialized using `seq` constructor, not `new`. Also removed redundant invariant in the `while` loop that was causing issues with sequence updates. */
{
    var len1 := |c1|;
    var len2 := |c2|;
    var maxLen := Max(len1, len2);
    var r := seq(maxLen, _ => 0.0);

    var i := 0;
    while i < maxLen
        invariant 0 <= i <= maxLen
        invariant |r| == maxLen
        invariant forall k :: 0 <= k < i ==> (
            if k < len1 && k < len2 then
                r[k] == c1[k] - c2[k]
            else if k < len1 && k >= len2 then
                r[k] == c1[k]
            else if k >= len1 && k < len2 then
                r[k] == -c2[k]
            else
                false
        )
    {
        if i < len1 && i < len2 {
            r := r[i := c1[i] - c2[i]];
        } else if i < len1 && i >= len2 {
            r := r[i := c1[i]];
        } else if i >= len1 && i < len2 {
            r := r[i := -c2[i]];
        }
        // The case where r[i] is 0.0 is handled by initialization
        i := i + 1;
    }
    return r;
}
// </vc-code>
