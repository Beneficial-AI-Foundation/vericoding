// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

// <vc-helpers>
// No helpers required for verification.
// </vc-helpers>

// <vc-spec>
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    // TODO: modify the ensures clause so that max is indeed equal to the longest increasing subsequence
    ensures max >= 1
// </vc-spec>
// <vc-code>
{
  var n := nums.Length;
  var dp := new int[n];
  var maxv := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> 1 <= dp[k] <= k + 1
    invariant 1 <= maxv <= n
  {
    var cur := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant 1 <= cur <= i + 1
      invariant forall k :: 0 <= k < j ==> 1 <= dp[k] <= k + 1
    {
      if nums[j] < nums[i] {
        if dp[j] + 1 > cur {
          cur := dp[j] + 1;
        }
      }
      j := j + 1;
    }
    dp[i] := cur;
    if dp[i] > maxv {
      maxv := dp[i];
    }
    i := i + 1;
  }
  max := maxv;
}
// </vc-code>

