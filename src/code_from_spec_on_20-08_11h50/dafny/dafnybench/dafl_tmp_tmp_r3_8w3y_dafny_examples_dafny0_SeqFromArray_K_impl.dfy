method K(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length && n <= c.Length
// </vc-spec>
// <vc-code>
{
}
// </vc-code>

method M'(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{
  if {
    case l+m <= c.Length && forall i :: 0 <= i < m ==> a[i] == c[l+i] =>
      assert a[..m] == c[l..l+m];
    case l+a.Length <= c.Length && forall i :: k <= i < a.Length ==> a[i] == c[l+i] =>
      assert a[k..] == c[l+k..l+a.Length];
    case l+k+m <= c.Length && forall i :: k <= i < k+m ==> a[i] == c[l+i] =>
      assert a[k..k+m] == c[l+k..l+k+m];
    case true =>
  }
}