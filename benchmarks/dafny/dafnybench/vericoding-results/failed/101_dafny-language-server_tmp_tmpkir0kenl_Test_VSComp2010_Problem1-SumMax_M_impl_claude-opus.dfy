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
// Helper function to compute the sum of array elements from 0 to n-1
function Sum(a: array<int>, n: int): int
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0 else Sum(a, n-1) + a[n-1]
}
// </vc-helpers>

// <vc-spec>
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
// </vc-spec>
// <vc-code>
{
  sum := 0;
  max := 0;
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant sum == Sum(a, i)
    invariant forall k :: 0 <= k < i ==> a[k] <= max
    invariant i == 0 || (exists k :: 0 <= k < i && a[k] == max)
    invariant sum <= i * max
  {
    if i == 0 || a[i] > max {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}
// </vc-code>

