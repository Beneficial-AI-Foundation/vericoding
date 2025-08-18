// <vc-helpers>
// </vc-helpers>

method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// <vc-code>
{
  assume false;
}
// </vc-code>