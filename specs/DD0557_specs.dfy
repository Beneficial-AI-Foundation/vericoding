// <vc-preamble>
// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// /autoTriggers:1 added to suppress instabilities
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method L(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length == c.Length
// </vc-spec>
// <vc-code>
{
  var A := a[n..];
  var C := c[n..];
  var h := a.Length - n;
  if {
    case A == C =>
      assert forall i :: 0 <= i < h ==> A[i] == C[i];
    case A == C =>
      assert forall i :: n <= i < n + h ==> a[i] == c[i];
    case true =>
  }
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