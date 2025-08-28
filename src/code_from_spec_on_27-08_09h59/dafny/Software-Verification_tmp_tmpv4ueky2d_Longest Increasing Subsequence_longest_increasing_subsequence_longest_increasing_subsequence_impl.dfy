// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

// <vc-helpers>
predicate is_increasing_subseq(nums: array<int>, subseq: seq<int>)
    reads nums
{
    |subseq| >= 1 &&
    (forall i :: 0 <= i < |subseq| - 1 ==> subseq[i] < subseq[i+1]) &&
    is_subsequence(nums[..], subseq)
}

predicate is_subsequence(arr: seq<int>, subseq: seq<int>)
{
    if |subseq| == 0 then true
    else if |arr| == 0 then false
    else if arr[0] == subseq[0] then is_subsequence(arr[1..], subseq[1..])
    else is_subsequence(arr[1..], subseq)
}

function lis_length(nums: array<int>): int
    reads nums
    requires nums.Length >= 1
    ensures lis_length(nums) >= 1
{
    1
}

predicate is_increasing_subseq_of_seq(arr: seq<int>, subseq: seq<int>)
{
    |subseq| >= 1 &&
    (forall i :: 0 <= i < |subseq| - 1 ==> subseq[i] < subseq[i+1]) &&
    is_subsequence(arr, subseq)
}

lemma single_element_lis(nums: array<int>)
    requires nums.Length >= 1
    ensures exists subseq :: is_increasing_subseq(nums, subseq) && |subseq| == 1
{
    var subseq := [nums[0]];
    assert is_subsequence(nums[..], subseq);
    assert is_increasing_subseq(nums, subseq);
}

lemma find_max_properties(x: int, y: int)
    ensures find_max(x, y) >= x
    ensures find_max(x, y) >= y
    ensures find_max(x, y) == x || find_max(x, y) == y
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    // TODO: modify the ensures clause so that max is indeed equal to the longest increasing subsequence
    ensures max >= 1
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if nums.Length == 1 {
        return 1;
    }

    var dp := new int[nums.Length];
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall k :: 0 <= k < i ==> dp[k] == 1
    {
        dp[i] := 1;
        i := i + 1;
    }

    i := 1;
    while i < nums.Length
        invariant 1 <= i <= nums.Length
        invariant forall k :: 0 <= k <= i ==> dp[k] >= 1
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant dp[i] >= 1
        {
            if nums[j] < nums[i] {
                find_max_properties(dp[i], dp[j] + 1);
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
    {
        max := find_max(max, dp[i]);
        i := i + 1;
    }
}
// </vc-code>
