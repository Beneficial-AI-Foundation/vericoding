// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant forall j :: 0 <= j < i ==> a[j] + 1 != a[j + 1]
  {
    if a[i] + 1 == a[i + 1] {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
