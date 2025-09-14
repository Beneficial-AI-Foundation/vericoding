

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// </vc-spec>
// <vc-code>
{
  x := -1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j | 0 <= j < i :: a[j] != 'e'
    invariant x == -1
  {
    if a[i] == 'e' {
      x := i;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

