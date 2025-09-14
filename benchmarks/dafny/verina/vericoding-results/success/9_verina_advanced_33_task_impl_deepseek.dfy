// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsGreaterThanIfInSequence(nums: array<int>, i: int, prevIndex: int): bool
  requires 0 <= prevIndex < i < nums.Length
  reads nums
{
  nums[i] > nums[prevIndex]
}

function SeqLengthAt(nums: array<int>, dp: array<int>, i: int): int
  requires 0 <= i < nums.Length
  requires dp.Length == nums.Length
  requires forall j :: 0 <= j < dp.Length ==> dp[j] >= 1
  reads dp
{
  dp[i]
}

predicate ValidLISLength(len: int, nums: array<int>)
{
  len >= 0 && (nums.Length == 0 ==> len == 0)
}

lemma MaintainsDPInvariant(nums: array<int>, dp: array<int>, i: int, j: int)
  requires 0 <= i <= nums.Length
  requires dp.Length == nums.Length
  requires forall k :: 0 <= k < i ==> dp[k] >= 1
  requires 0 <= j <= i
  requires i < nums.Length ==> dp[i] >= 1
  ensures forall k :: 0 <= k < i ==> dp[k] >= 1
{
  /* helper modified by LLM (iteration 4): Fixed lemma to properly handle dp array bounds */
}

lemma InitializeDPInvariant(nums: array<int>, dp: array<int>, i: int)
  requires 0 <= i <= nums.Length
  requires dp.Length == nums.Length
  requires forall k :: 0 <= k < i ==> dp[k] >= 1
  ensures forall k :: 0 <= k < i ==> dp[k] >= 1
{
  /* helper modified by LLM (iteration 4): Added lemma for initial dp invariant */
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures nums.Length == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Fixed loop invariants and array bounds */
  if nums.Length == 0 {
    result := 0;
    return;
  }
  
  var dp := new int[nums.Length];
  var maxLength := 1;
  
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall j :: 0 <= j < i ==> dp[j] >= 1
    invariant maxLength >= 1
  {
    dp[i] := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= 1
      invariant forall k :: 0 <= k < i ==> dp[k] >= 1
    {
      if nums[j] < nums[i] && dp[j] + 1 > dp[i] {
        dp[i] := dp[j] + 1;
      }
      j := j + 1;
    }
    if dp[i] > maxLength {
      maxLength := dp[i];
    }
    i := i + 1;
  }
  
  result := maxLength;
}
// </vc-code>
