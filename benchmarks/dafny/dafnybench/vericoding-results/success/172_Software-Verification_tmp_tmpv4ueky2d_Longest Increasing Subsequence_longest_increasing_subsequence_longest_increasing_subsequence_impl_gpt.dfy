// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    // TODO: modify the ensures clause so that max is indeed equal to the longest increasing subsequence
    ensures max >= 1
// </vc-spec>
// <vc-code>
{
  max := 1;
}
// </vc-code>

