/*
https://leetcode.com/problems/find-pivot-index/description/
Given an array of integers nums, calculate the pivot index of this array.

The pivot index is the index where the sum of all the numbers strictly to the left of the index is equal to the sum of all the numbers strictly to the index's right.

If the index is on the left edge of the array, then the left sum is 0 because there are no elements to the left. This also applies to the right edge of the array.

Return the leftmost pivot index. If no such index exists, return -1.



Example 1:

Input: nums = [1,7,3,6,5,6]
Output: 3
Explanation:
The pivot index is 3.
Left sum = nums[0] + nums[1] + nums[2] = 1 + 7 + 3 = 11
Right sum = nums[4] + nums[5] = 5 + 6 = 11
Example 2:

Input: nums = [1,2,3]
Output: -1
Explanation:
There is no index that satisfies the conditions in the problem statement.
Example 3:

Input: nums = [2,1,-1]
Output: 0
Explanation:
The pivot index is 0.
Left sum = 0 (no elements to the left of index 0)
Right sum = nums[1] + nums[2] = 1 + -1 = 0

```TypeScript
function pivotIndex(nums: number[]): number {
    const n = nums.length;
    let leftsums = [0], rightsums = [0];
    for(let i=1; i < n+1; i++) {
        leftsums.push(nums[i-1]+leftsums[i-1]);
        rightsums.push(nums[n-i]+rightsums[i-1]);
    }
    for(let i=0; i <= n; i++) {
        if(leftsums[i] == rightsums[n-(i+1)]) return i;
    }
    return -1;
};
```
*/

function sum(nums: seq<int>): int {
    // if |nums| == 0 then 0 else nums[0]+sum(nums[1..])
    if |nums| == 0 then 0 else sum(nums[0..(|nums|-1)])+nums[|nums|-1]
}


function sumUp(nums: seq<int>): int {
    if |nums| == 0 then 0 else nums[0]+sumUp(nums[1..])
}

// By Divyanshu Ranjan

// By Divyanshu Ranjan

// <vc-helpers>
function SumPrefix(nums: seq<int>, k: nat): int
    requires k <= |nums|
{
    if k == 0 then 0 else SumPrefix(nums, k-1) + nums[k-1]
}

lemma SumPrefixCorrect(nums: seq<int>, k: nat)
    requires k <= |nums|
    ensures SumPrefix(nums, k) == sum(nums[0..k])
{
    if k == 0 {
        assert SumPrefix(nums, 0) == 0;
        assert sum(nums[0..0]) == 0;
    } else {
        SumPrefixCorrect(nums, k-1);
        assert SumPrefix(nums, k) == SumPrefix(nums, k-1) + nums[k-1];
        assert sum(nums[0..k]) == sum(nums[0..k-1]) + nums[k-1];
    }
}

lemma SumSuffixCorrect(nums: seq<int>, k: nat)
    requires k <= |nums|
    ensures sum(nums[k..]) == if k == |nums| then 0 else nums[k] + sum(nums[k+1..])
{
    if k == |nums| {
        assert sum(nums[k..]) == 0;
    } else {
        assert sum(nums[k..]) == nums[k] + sum(nums[k+1..]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method  FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindPivotIndexImpl(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{
    var totalSum := 0;
    for i := 0 to |nums|
        invariant totalSum == SumPrefix(nums, i)
    {
        totalSum := totalSum + nums[i];
    }
    SumPrefixCorrect(nums, |nums|);
    assert totalSum == sum(nums[0..|nums|]);

    var leftSum := 0;
    for i := 0 to |nums|
        invariant leftSum == SumPrefix(nums, i)
        invariant forall k: nat :: k < i ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    {
        var rightSum := totalSum - leftSum - nums[i];
        SumPrefixCorrect(nums, i);
        assert sum(nums[0..i]) == leftSum;
        if i + 1 <= |nums| {
            SumSuffixCorrect(nums, i+1);
            assert sum(nums[(i+1)..]) == rightSum;
        } else {
            assert sum(nums[(i+1)..]) == 0;
            assert sum(nums[(i+1)..]) == rightSum;
        }
        if leftSum == rightSum {
            assert sum(nums[0..i]) == leftSum;
            assert sum(nums[(i+1)..]) == rightSum;
            return i;
        }
        leftSum := leftSum + nums[i];
    }
    return -1;
}
// </vc-code>
