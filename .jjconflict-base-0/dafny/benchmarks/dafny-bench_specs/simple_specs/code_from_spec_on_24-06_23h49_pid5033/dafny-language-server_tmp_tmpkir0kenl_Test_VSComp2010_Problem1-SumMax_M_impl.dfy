// IMPL
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array. The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

method M(N: int, a: array<int>) returns (sum: int, max: int)
 requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k])
 ensures sum <= N * max
{
  if N == 0 {
    sum := 0;
    max := 0;
    return;
  }
  
  sum := 0;
  max := a[0];
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant max >= 0
    invariant sum >= 0
    invariant forall k :: 0 <= k < i ==> a[k] <= max
    invariant sum <= i * max
  {
    if a[i] > max {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}