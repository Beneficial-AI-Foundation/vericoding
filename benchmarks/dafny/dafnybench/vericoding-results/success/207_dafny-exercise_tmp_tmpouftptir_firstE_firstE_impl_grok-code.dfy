

// <vc-helpers>
// Empty as parsed code block was invalid
// </vc-helpers>

// <vc-spec>
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j | 0 <= j < i :: a[j] != 'e'
  {
    if a[i] == 'e' {
      x := i;
      return;
    }
    i := i + 1;
  }
  x := -1;
}
// </vc-code>

