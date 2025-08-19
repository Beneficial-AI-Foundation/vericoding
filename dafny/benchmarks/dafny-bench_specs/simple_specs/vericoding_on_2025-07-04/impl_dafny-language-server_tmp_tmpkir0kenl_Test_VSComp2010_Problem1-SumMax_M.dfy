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
    invariant sum == (if i == 0 then 0 else (sum_of_elements(a, i)))
    invariant max >= (if i == 0 then a[0] else max_of_elements(a, i))
    invariant sum <= i * max
  {
    if a[i] > max {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}

function sum_of_elements(a: array<int>, n: int): int
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0 else sum_of_elements(a, n-1) + a[n-1]
}

function max_of_elements(a: array<int>, n: int): int
  requires 0 < n <= a.Length
  reads a
{
  if n == 1 then a[0] else 
    var prev_max := max_of_elements(a, n-1);
    if a[n-1] > prev_max then a[n-1] else prev_max
}