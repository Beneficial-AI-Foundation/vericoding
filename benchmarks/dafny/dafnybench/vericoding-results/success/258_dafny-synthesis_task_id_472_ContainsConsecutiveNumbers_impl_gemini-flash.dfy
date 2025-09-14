

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant forall k :: 0 <= k < i ==> a[k] + 1 != a[k+1]
  {
    if a[i] + 1 == a[i+1] {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

