

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
// </vc-spec>
// <vc-code>
{
  if |x| == 0 {
    return true;
  }
  
  var j := 0;
  while j < |x| / 2
    invariant 0 <= j <= |x| / 2
    invariant forall i :: 0 <= i < j ==> x[i] == x[|x| - i - 1]
  {
    if x[j] != x[|x| - j - 1] {
      return false;
    }
    j := j + 1;
  }
  
  return true;
}
// </vc-code>

