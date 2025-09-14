

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// </vc-spec>
// <vc-code>
{
  var i := 0;
  x := -1;
  while i < a.Length && a[i] != 'e'
    invariant 0 <= i <= a.Length
    invariant forall j | 0 <= j < i :: a[j] != 'e'
    decreases a.Length - i
  {
    i := i + 1;
  }
  if i < a.Length {
    x := i;
  } else {
    x := -1;
  }
}
// </vc-code>

