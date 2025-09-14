

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |x| / 2
    invariant 0 <= i <= |x| / 2
    invariant forall j :: 0 <= j < i ==> x[j] == x[|x| - 1 - j]
  {
    if x[i] != x[|x| - i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

