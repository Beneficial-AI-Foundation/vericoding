//ATOM
// Function
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
  
  // Initialize all dp values to 1
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall k :: 0 <= k < i ==> dp[k] == 1
  {
    dp[i] := 1;
    i := i + 1;
  }
  
  // Fill dp array
  i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant forall k :: 0 <= k < nums.Length ==> dp[k] >= 1
    invariant forall k :: i <= k < nums.Length ==> dp[k] == 1
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= 1
      invariant forall k :: 0 <= k < nums.Length ==> dp[k] >= 1
    {
      if nums[j] < nums[i] {
        dp[i] := find_max(dp[i], dp[j] + 1);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Find maximum value in dp array
  max := dp[0];
  i := 1;
  while i < nums.Length
    invariant 1 <= i <= nums.Length
    invariant max >= 1
    invariant forall k :: 0 <= k < i ==> max >= dp[k]
    invariant forall k :: 0 <= k < nums.Length ==> dp[k] >= 1
    /* code modified by LLM (iteration 1): fixed invariant to ensure max equals some dp value seen so far */
    invariant exists k :: 0 <= k < i && max == dp[k]
  {
    /* code modified by LLM (iteration 1): added assertion to help verification understand max update */
    if dp[i] > max {
      max := dp[i];
    }
    i := i + 1;
  }
}