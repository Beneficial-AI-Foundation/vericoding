// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed preconditions for MaxOfSeq to handle slices correctly */
predicate IsIncreasingSubsequence(nums: array<int>, indices: seq<int>)
    reads nums
    requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < nums.Length
{
    forall i, j :: 0 <= i < j < |indices| ==>
        indices[i] < indices[j] && nums[indices[i]] < nums[indices[j]]
}

function MaxLISEndingAt(nums: array<int>, k: int, dp: seq<int>): int
    reads nums
    requires 0 <= k < nums.Length
    requires |dp| == k
    requires forall i :: 0 <= i < k ==> 0 <= dp[i] <= i + 1
{
    if k == 0 then 1
    else
        var maxLen := 1;
        var maxLenRec := MaxLISFromPrevious(nums, k, dp, k - 1, 1);
        maxLenRec
}

function MaxLISFromPrevious(nums: array<int>, k: int, dp: seq<int>, j: int, currentMax: int): int
    reads nums
    requires 0 <= k < nums.Length
    requires |dp| == k
    requires forall i :: 0 <= i < |dp| ==> 0 <= dp[i] <= i + 1
    requires -1 <= j < k
    requires currentMax >= 1
    decreases j + 1
{
    if j < 0 then currentMax
    else if j < |dp| && nums[j] < nums[k] then
        var newMax := if dp[j] + 1 > currentMax then dp[j] + 1 else currentMax;
        MaxLISFromPrevious(nums, k, dp, j - 1, newMax)
    else
        MaxLISFromPrevious(nums, k, dp, j - 1, currentMax)
}

function MaxOfSeq(s: seq<int>, maxBound: int): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    requires forall i :: 0 <= i < |s| ==> s[i] <= maxBound
    requires maxBound >= 0
    ensures MaxOfSeq(s, maxBound) >= 0
    ensures forall i :: 0 <= i < |s| ==> MaxOfSeq(s, maxBound) >= s[i]
    ensures MaxOfSeq(s, maxBound) <= maxBound
{
    if |s| == 0 then 0
    else if |s| == 1 then s[0]
    else
        var tailMax := MaxOfSeq(s[1..], maxBound);
        if s[0] > tailMax then s[0] else tailMax
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= nums.Length
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Pass nums.Length as maxBound to MaxOfSeq */
    if nums.Length == 0 {
        result := 0;
    } else {
        var dp := [];
        var i := 0;
        while i < nums.Length
            invariant 0 <= i <= nums.Length
            invariant |dp| == i
            invariant forall j :: 0 <= j < i ==> 0 <= dp[j] <= j + 1
            invariant forall j :: 0 <= j < i ==> dp[j] <= nums.Length
        {
            var maxLen := 1;
            var j := 0;
            while j < i
                invariant 0 <= j <= i
                invariant maxLen >= 1
                invariant maxLen <= j + 1
                invariant maxLen <= i + 1
            {
                if nums[j] < nums[i] && dp[j] + 1 > maxLen {
                    maxLen := dp[j] + 1;
                }
                j := j + 1;
            }
            assert maxLen <= i + 1;
            assert i + 1 <= nums.Length;
            dp := dp + [maxLen];
            i := i + 1;
        }
        assert |dp| == nums.Length;
        assert forall j :: 0 <= j < |dp| ==> dp[j] <= nums.Length;
        result := MaxOfSeq(dp, nums.Length);
    }
}
// </vc-code>
