// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

// <vc-helpers>
function PrefixSum(a: array<int>, n: int): int
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0 else PrefixSum(a, n - 1) + a[n - 1]
}

lemma Sum_le_mul(a: array<int>, n: int, m: int)
  requires 0 <= n <= a.Length
  requires forall j :: 0 <= j && j < n ==> a[j] <= m
  ensures PrefixSum(a, n) <= n * m
  decreases n
{
  if n == 0 {
  } else {
    Sum_le_mul(a, n - 1, m);
    assert PrefixSum(a, n) == PrefixSum(a, n - 1) + a[n - 1];
    assert PrefixSum(a, n - 1) <= (n - 1) * m;
    assert a[n - 1] <= m;
    assert PrefixSum(a, n - 1) + a[n - 1] <= (n - 1) * m + m;
  }
}

lemma Forall_le_implies(a: array<int>, n: int, x: int, y: int)
  requires 0 <= n <= a.Length
  requires forall j :: 0 <= j && j < n ==> a[j] <= x
  requires x <= y
  ensures forall j :: 0 <= j && j < n ==> a[j] <= y
  decreases n
{
  if n == 0 {
  } else {
    Forall_le_implies(a, n - 1, x, y);
    assert a[n - 1] <= x;
    assert x <= y;
    assert a[n - 1] <= y;
  }
}
// </vc-helpers>

// <vc-spec>
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
// </vc-spec>
// <vc-code>
{
  if N == 0 {
    sum := 0;
    max := 0;
    return;
  }
  sum := a[0];
  max := a[0];
  var i := 1;
  while i < N
    invariant 0 <= i <= N
    invariant sum == PrefixSum(a, i)
    invariant forall j :: 0 <= j < i ==> a[j] <= max
  {
    var v := a[i];
    if v <= max {
      sum := sum + v;
      i := i + 1;
    } else {
      assert max < v;
      Forall_le_implies(a, i, max, v);
      sum := sum + v;
      max := v;
      i := i + 1;
    }
  }
  Sum_le_mul(a, N, max);
  assert sum <= N * max;
}
// </vc-code>

