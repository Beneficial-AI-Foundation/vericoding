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
lemma sumEmpty()
    ensures sum([]) == 0
{
}

lemma sumSingleton(x: int)
    ensures sum([x]) == x
{
    assert [x] == [x][0..0] + [x];
    assert [x][0..0] == [];
}

lemma sumAppend(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        sumSingleton(x);
    } else {
        var s' := s + [x];
        assert s'[0..|s'|-1] == s;
        assert s'[|s'|-1] == x;
    }
}

lemma sumSplit(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    ensures sum(s) == sum(s[0..i]) + sum(s[i..])
{
    if i == 0 {
        assert s[0..i] == [];
        assert s[i..] == s;
        sumEmpty();
    } else if i == |s| {
        assert s[0..i] == s;
        assert s[i..] == [];
        sumEmpty();
    } else if |s| == 0 {
        // impossible due to requires
    } else {
        var prefix := s[0..i];
        var suffix := s[i..];
        
        if |suffix| == 0 {
            assert s == prefix;
        } else {
            assert s == prefix + suffix;
            sumConcat(prefix, suffix);
        }
    }
}

lemma sumConcat(s1: seq<int>, s2: seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if |s2| == 0 {
        assert s1 + s2 == s1;
    } else {
        var combined := s1 + s2;
        var lastIdx := |combined| - 1;
        var withoutLast := combined[0..lastIdx];
        
        assert combined[lastIdx] == s2[|s2|-1];
        assert withoutLast == s1 + s2[0..|s2|-1];
        
        sumConcat(s1, s2[0..|s2|-1]);
    }
}
// </vc-helpers>

// <vc-spec>
method  FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall k: nat :: k < i ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    {
        var leftSum := sum(nums[0..i]);
        var rightSum := sum(nums[(i+1)..]);
        
        if leftSum == rightSum {
            index := i;
            return;
        }
        i := i + 1;
    }
    
    index := -1;
}
// </vc-code>

