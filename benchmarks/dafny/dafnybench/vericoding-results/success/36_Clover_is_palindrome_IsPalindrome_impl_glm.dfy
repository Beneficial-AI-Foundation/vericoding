

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
// </vc-spec>
// <vc-code>
{
  var n := |x|;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant forall j :: 0 <= j < n && (j < i || j >= n - i) ==> x[j] == x[n - j - 1]
  {
    if x[i] != x[n - i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

