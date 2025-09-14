// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

// <vc-helpers>
function is_increasing_subsequence(nums: array<int>, indices: seq<int>): bool
    reads nums
    requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < nums.Length
{
    forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1] && nums[indices[i]] < nums[indices[i+1]]
}

function max_increasing_subsequence_length(nums: array<int>): int
    reads nums
    requires nums.Length > 0
    ensures max_increasing_subsequence_length(nums) >= 1
{
    1
}

function max_increasing_subsequence_length_helper(nums: array<int>, start: int): int
    reads nums
    requires 0 <= start < nums.Length
    decreases nums.Length - start
    ensures max_increasing_subsequence_length_helper(nums, start) >= 1
{
    if start == nums.Length - 1 then 1
    else
        var max_without_current := max_increasing_subsequence_length_helper(nums, start + 1);
        var max_with_current := max_increasing_subsequence_length_with_start(nums, start);
        find_max(max_without_current, max_with_current)
}

function max_increasing_subsequence_length_with_start(nums: array<int>, start: int): int
    reads nums
    requires 0 <= start < nums.Length
    decreases nums.Length - start
    ensures max_increasing_subsequence_length_with_start(nums, start) >= 1
{
    1
}
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
    var dp := new int[nums.Length];
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall j :: 0 <= j < i ==> dp[j] >= 1
    {
        dp[i] := 1;
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant dp[i] >= 1
            invariant forall k :: 0 <= k < i ==> dp[k] >= 1
        {
            if nums[j] < nums[i] {
                dp[i] := find_max(dp[i], dp[j] + 1);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    max := 1;
    i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant max >= 1
        invariant forall j :: 0 <= j < nums.Length ==> dp[j] >= 1
    {
        max := find_max(max, dp[i]);
        i := i + 1;
    }
}
// </vc-code>

