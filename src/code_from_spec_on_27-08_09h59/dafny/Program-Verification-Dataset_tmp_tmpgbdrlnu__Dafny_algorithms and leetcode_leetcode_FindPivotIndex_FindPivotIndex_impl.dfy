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
lemma SumAdditive(nums: seq<int>, i: nat, j: nat)
    requires i <= j <= |nums|
    ensures sum(nums[0..i]) + sum(nums[i..j]) == sum(nums[0..j])
    decreases j - i
{
    if i == j {
        assert nums[i..j] == [];
        assert sum(nums[i..j]) == 0;
        assert nums[0..i] == nums[0..j];
    } else if i == 0 {
        SumAppend(nums[0..j], i);
    } else {
        SumAppend(nums[0..j], i);
    }
}

lemma SumAppend(nums: seq<int>, split: nat)
    requires split <= |nums|
    ensures sum(nums[0..split]) + sum(nums[split..]) == sum(nums)
{
    if split == |nums| {
        assert nums[split..] == [];
        assert sum(nums[split..]) == 0;
        assert nums[0..split] == nums;
    } else if split == 0 {
        assert nums[0..split] == [];
        assert sum(nums[0..split]) == 0;
        assert nums[split..] == nums;
    } else {
        var prefix := nums[0..split];
        var suffix := nums[split..];
        assert nums == prefix + suffix;
        SumConcat(prefix, suffix);
    }
}

lemma SumEmpty()
    ensures sum([]) == 0
{
}

lemma SumSingle(x: int)
    ensures sum([x]) == x
{
}

lemma SumConcat(a: seq<int>, b: seq<int>)
    ensures sum(a + b) == sum(a) + sum(b)
    decreases |a| + |b|
{
    if |a| == 0 {
        assert a + b == b;
    } else if |b| == 0 {
        assert a + b == a;
    } else {
        var combined := a + b;
        var n := |combined|;
        assert n > 0;
        assert combined[n-1] == b[|b|-1];
        
        if |a| == 1 {
            assert sum(combined) == sum(combined[0..n-1]) + combined[n-1];
            assert combined[0..n-1] == b[0..|b|-1];
            assert a[0..|a|-1] == [];
            SumConcat([], b[0..|b|-1]);
        } else {
            var a_init := a[0..|a|-1];
            var a_last := a[|a|-1];
            assert a == a_init + [a_last];
            assert a + b == a_init + ([a_last] + b);
            SumConcat(a_init, [a_last] + b);
            SumConcat([a_last], b);
        }
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
{
    var n := |nums|;
    
    for i := 0 to n
        invariant 0 <= i <= n
        invariant forall k: nat :: k < i ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    {
        var leftSum := sum(nums[0..i]);
        var rightSum := sum(nums[(i+1)..]);
        
        if leftSum == rightSum {
            return i;
        }
    }
    
    return -1;
}
// </vc-code>
