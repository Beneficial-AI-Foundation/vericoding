// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsPalindromeImpl(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
{
  if |x| == 0 {
    return true;
  }
  
  var i := 0;
  var len := |x|;
  while i < len / 2
    invariant 0 <= i <= len / 2
    invariant forall k :: 0 <= k < i ==> x[k] == x[len - k - 1]
  {
    if x[i] != x[len - i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
