function find_max(x: int, y: int): int
{
  if x > y then x
  else y
}


//IMPL longest_increasing_subsequence
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
  requires 1 <= nums.Length <= 2500
  requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
  // TODO: modify the ensures clause so that max is indeed equal to the longest increasing subsequence
  ensures max >= 1
{
  var dp := new int[nums.Length];
  var i := 0;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall k :: 0 <= k < i ==> dp[k] >= 1
  {
    dp[i] := 1;
    i := i + 1;
  }
  
  i := 1;
  /* code modified by LLM (iteration 1): strengthened invariant to ensure dp[i] >= 1 is maintained */
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant forall k :: 0 <= k < nums.Length ==> dp[k] >= 1
    invariant dp[i] >= 1
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= 1
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
  {
    max := find_max(max, dp[i]);
    i := i + 1;
  }
}