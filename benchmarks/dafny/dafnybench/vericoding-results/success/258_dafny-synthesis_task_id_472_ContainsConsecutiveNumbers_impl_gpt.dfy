

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
// </vc-spec>
// <vc-code>
{
  var found := false;
  var w := -1;
  var i := 0;
  while i + 1 < a.Length
    invariant 0 <= i <= a.Length - 1
    invariant (!found ==> w == -1)
    invariant (found ==> 0 <= w < a.Length - 1 && a[w] + 1 == a[w + 1])
    invariant (!found ==> (forall j :: 0 <= j < i ==> a[j] + 1 != a[j + 1]))
    decreases a.Length - i
  {
    if !found && a[i] + 1 == a[i + 1] {
      found := true;
      w := i;
    }
    i := i + 1;
  }
  if !found {
    assert i + 1 >= a.Length;
    assert i >= a.Length - 1;
    forall j | 0 <= j < a.Length - 1
      ensures a[j] + 1 != a[j + 1]
    {
      assert j < i;
    }
  }
  result := found;
}
// </vc-code>

