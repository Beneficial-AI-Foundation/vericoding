

// <vc-helpers>
lemma palindrome_property(s: string, i: int, j: int)
  requires 0 <= i <= j < |s|
  requires forall k : int :: i <= k <= j ==> s[k] == s[|s| - k - 1]
  ensures forall k : int :: i <= k <= j ==> s[k] == s[|s| - k - 1]
{
}
// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |text|;
  if n == 0 {
    return true;
  }
  
  var i := 0;
  var j := n - 1;
  
  while i < j
    invariant 0 <= i <= j < n
    invariant forall k : int :: 0 <= k < i ==> text[k] == text[n - k - 1]
  {
    if text[i] != text[j] {
      return false;
    }
    i := i + 1;
    j := j - 1;
  }
  
  return true;
}
// </vc-code>

