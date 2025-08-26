// <vc-spec>
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    // TODO: modify the ensures clause so that max is indeed equal to the longest increasing subsequence
    ensures max >= 1
// </vc-spec>
// <vc-code>
{
    var dp := new int[nums.Length];
    
    // Initialize dp array - each element forms a subsequence of length 1
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall k :: 0 <= k < i ==> dp[k] == 1
    {
        dp[i] := 1;
        i := i + 1;
    }
    
    // Fill dp array using dynamic programming
    i := 1;
    while i < nums.Length
        invariant 1 <= i <= nums.Length
        invariant forall k :: 0 <= k < nums.Length ==> dp[k] >= 1
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant dp[i] >= 1
            invariant forall k :: 0 <= k < nums.Length ==> dp[k] >= 1
        {
            if nums[j] < nums[i] {
                dp[i] := find_max(dp[i], dp[j] + 1);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Find maximum value in dp array
    max := dp[0];
    i := 1;
    while i < nums.Length
        invariant 1 <= i <= nums.Length
        invariant max >= 1
        invariant exists k :: 0 <= k < i && dp[k] == max
        invariant forall k :: 0 <= k < i ==> dp[k] <= max
    {
        max := find_max(max, dp[i]);
        i := i + 1;
    }
}
// </vc-code>

// <vc-helpers>
function maxPrevValue(nums: array<int>, dp: array<int>, k: int): int
    requires 0 <= k < nums.Length
    requires 0 <= k < dp.Length
    reads nums, dp
{
    if k == 0 then 0
    else maxPrevValueHelper(nums, dp, k, 0, 0)
}

function maxPrevValueHelper(nums: array<int>, dp: array<int>, k: int, j: int, currentMax: int): int
    requires 0 <= k < nums.Length
    requires 0 <= k < dp.Length
    requires 0 <= j <= k
    reads nums, dp
    decreases k - j
{
    if j == k then currentMax
    else if nums[j] < nums[k] && dp[j] > currentMax then
        maxPrevValueHelper(nums, dp, k, j + 1, dp[j])
    else
        maxPrevValueHelper(nums, dp, k, j + 1, currentMax)
}
// </vc-helpers>

// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}