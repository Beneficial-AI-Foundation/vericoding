// <vc-preamble>
function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `blockSize` calculation is correct, and the predicate correctly uses `isPalindrome`. No changes are needed in helper. */
predicate IsBlockPalindrome(s: string, k: int, blockIndex: int)
    requires k > 0
    requires |s| % k == 0
    requires 0 <= blockIndex < k
{
    var blockSize := |s| / k;
    var start := blockIndex * blockSize;
    var end := (blockIndex + 1) * blockSize;
    isPalindrome(s[start..end])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires k > 0
    ensures result == "YES" || result == "NO"
    ensures |s| % k != 0 ==> result == "NO"
    ensures |s| % k == 0 && (forall i :: 0 <= i < k ==> 
        isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "YES"
    ensures |s| % k == 0 && (exists i :: 0 <= i < k && 
        !isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "NO"
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the `k == 0` check; it should be `k <= 0`. Also, removed `k == 0` from the loop invariant given the guard. */
{
  if k <= 0 || |s| % k != 0 {
    return "NO";
  }

  var blockSize := |s| / k;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant k > 0
    invariant |s| % k == 0
    invariant forall j :: 0 <= j < i ==> IsBlockPalindrome(s, k, j)
  {
    if !IsBlockPalindrome(s, k, i) {
      return "NO";
    }
    i := i + 1;
  }

  return "YES";
}
// </vc-code>
