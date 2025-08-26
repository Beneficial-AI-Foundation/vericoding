/*
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
*/

function sum(nums: seq<int>): int {
    // if |nums| == 0 then 0 else nums[0]+sum(nums[1..])
    if |nums| == 0 then 0 else sum(nums[0..(|nums|-1)])+nums[|nums|-1]
}


function sumUp(nums: seq<int>): int {
    if |nums| == 0 then 0 else nums[0]+sumUp(nums[1..])
}

// By Divyanshu Ranjan
lemma sumUpLemma(a: seq<int>, b: seq<int>)
  ensures sumUp(a + b) == sumUp(a) + sumUp(b)
{
  if a == [] {
     assert a + b == b;
  }
  else {
    sumUpLemma(a[1..], b);
    calc {
      sumUp(a + b);
      {
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
      }
      a[0] + sumUp(a[1..] + b);
      a[0] + sumUp(a[1..]) + sumUp(b);
    }
  }
}

// By Divyanshu Ranjan
lemma sumsEqual(nums: seq<int>)
  decreases |nums|
  ensures sum(nums) == sumUp(nums)
{
  if nums == [] {}
  else {
    var ln := |nums|-1;
    calc {
      sumUp(nums[..]);
      {
        assert nums[..] == nums[0..ln] + [nums[ln]];
        sumUpLemma(nums[0..ln], [nums[ln]]);
      }
      sumUp(nums[0..ln]) + sumUp([nums[ln]]);
      {
        assert forall a:: sumUp([a]) == a;
      }
      sumUp(nums[0..ln]) + nums[ln];
      {
        sumsEqual(nums[0..ln]);
      }
      sum(nums[0..ln]) + nums[ln];
    }
  }
}

// <vc-helpers>
function computeSum(nums: seq<int>, start: nat, end: nat): int
  requires start <= end <= |nums|
{
  sum(nums[start..end])
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