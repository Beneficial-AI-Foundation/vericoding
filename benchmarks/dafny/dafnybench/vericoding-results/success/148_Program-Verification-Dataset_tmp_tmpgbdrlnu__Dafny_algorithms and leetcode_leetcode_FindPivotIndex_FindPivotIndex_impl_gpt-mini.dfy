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
lemma SumEmpty(s: seq<int>)
  requires |s| == 0
  ensures sum(s) == 0
{
  // by definition of sum
}

lemma SumLast(s: seq<int>)
  requires |s| > 0
  ensures sum(s) == sum(s[0..|s|-1]) + s[|s|-1]
{
  // by definition of sum
}

lemma SumPrefixAdd(nums: seq<int>, i: int)
  requires 0 <= i < |nums|
  ensures sum(nums[0..i+1]) == sum(nums[0..i]) + nums[i]
{
  var s := nums[0..i+1];
  assert |s| == i+1;
  // |s| > 0 holds because i >= 0
  SumLast(s);
  // relate slices and last element of s back to nums
  assert s[0..|s|-1] == nums[0..i];
  assert s[|s|-1] == nums[i];
  assert sum(s) == sum(s[0..|s|-1]) + s[|s|-1];
  assert sum(nums[0..i+1]) == sum(nums[0..i]) + nums[i];
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
  var n := |nums|;
  var total := sum(nums);
  var left := 0;
  var i := 0;
  SumEmpty(nums[0..0]);
  assert left == sum(nums[0..i]);
  while i < n
    invariant 0 <= i <= n
    invariant left == sum(nums[0..i])
    invariant forall j :: 0 <= j < i ==> sum(nums[0..j]) != sum(nums[(j+1)..])
    decreases n - i
  {
    var right := sum(nums[(i+1)..]);
    if left == right {
      return i;
    } else {
      // record that this i is not a pivot
      assert left != right;
      // capture current i to help preserve invariants after update
      var i_old := i;
      // record the inequality in terms of nums and i_old so it remains valid after mutation
      assert left == sum(nums[0..i_old]);
      assert right == sum(nums[(i_old+1)..]);
      assert sum(nums[0..i_old]) != sum(nums[(i_old+1)..]);

      // update left and i, and reestablish the prefix-sum invariant
      left := left + nums[i_old];
      i := i_old + 1;
      if 0 < i {
        SumPrefixAdd(nums, i-1);
        assert left == sum(nums[0..i]);
      }
    }
  }
  return -1;
}
// </vc-code>

