predicate ValidInput(n: int, k: int, heights: seq<int>)
{
    n >= 1 && k >= 1 && |heights| == n && 
    forall i :: 0 <= i < |heights| ==> heights[i] >= 1
}

function CountEligible(heights: seq<int>, k: int): int
{
    |set i | 0 <= i < |heights| && heights[i] >= k :: i|
}

// <vc-helpers>
// No changes needed, as the duplicate function definition has been removed.
// The original function "CountEligible" is already defined at the top of the file.
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (count: int)
    requires ValidInput(n, k, heights)
    ensures 0 <= count <= |heights|
    ensures count == CountEligible(heights, k)
// </vc-spec>
// <vc-code>
{
    var num_eligible := 0;
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant 0 <= num_eligible <= i
        invariant num_eligible == CountEligible(heights[..i], k)
    {
        if heights[i] >= k {
            num_eligible := num_eligible + 1;
        }
    }
    return num_eligible;
}
// </vc-code>

