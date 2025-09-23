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
method M(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
// </vc-spec>
// <vc-code>
{
  var A := a[k..k+m];
  var C := c[l..l+n];
  if A == C {
    if * {
      assert m == n;
    } else if * {
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
    } else if * {
      assert forall i {:nowarn} :: k <= i < k+n ==> A[i-k] == C[i-k];
    } else if * {
      assert forall i :: 0 <= i < n ==> A[i] == a[k+i];
    } else if * {
      assert forall i :: 0 <= i < n ==> C[i] == c[l+i];
    } else if * {
      assert forall i {:nowarn} :: 0 <= i < n ==> a[k+i] == c[l+i];
    }
  }
}
// </vc-code>
