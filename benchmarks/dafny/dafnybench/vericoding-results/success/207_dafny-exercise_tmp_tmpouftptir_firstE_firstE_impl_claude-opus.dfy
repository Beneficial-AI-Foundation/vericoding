

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// </vc-spec>
// <vc-code>
{
  x := 0;
  while x < a.Length
    invariant 0 <= x <= a.Length
    invariant forall i | 0 <= i < x :: a[i] != 'e'
  {
    if a[x] == 'e' {
      return x;
    }
    x := x + 1;
  }
  x := -1;
}
// </vc-code>

