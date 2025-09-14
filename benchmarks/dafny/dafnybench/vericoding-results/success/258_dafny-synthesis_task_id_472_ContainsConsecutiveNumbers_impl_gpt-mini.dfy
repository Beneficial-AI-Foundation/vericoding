

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  while idx < a.Length - 1
    invariant 0 <= idx <= a.Length - 1
    invariant (forall j :: 0 <= j < idx ==> a[j] + 1 != a[j+1])
    decreases a.Length - idx
  {
    if a[idx] + 1 == a[idx + 1] {
      return true;
    }
    idx := idx + 1;
  }
  return false;
}
// </vc-code>

