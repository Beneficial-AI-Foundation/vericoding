

// <vc-helpers>
set-options "--allow-warnings true"
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> n > a[k]
    decreases a.Length - i
  {
    if n <= a[i] {
      ghost var w := i;
      assert 0 <= w < a.Length;
      assert n <= a[w];
      assert exists k :: 0 <= k < a.Length && n <= a[k];
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>

