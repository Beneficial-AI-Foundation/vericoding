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
function Sum(a: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= a.Length
  reads a
{
  if start == end then 0
  else Sum(a, start, end-1) + a[end-1]
}

lemma SumProperty(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  ensures Sum(a, start, end) == (if start == end then 0 else Sum(a, start, end-1) + a[end-1])
{
}

lemma SumBound(a: array<int>, start: int, end: int, max: int)
  requires 0 <= start <= end <= a.Length
  requires forall k :: start <= k < end ==> a[k] <= max
  ensures Sum(a, start, end) <= (end - start) * max
{
  if start == end {
  } else {
    SumBound(a, start, end-1, max);
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
  
  sum := 0;
  max := a[0];
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant sum == Sum(a, 0, i)
    invariant i > 0 ==> forall k :: 0 <= k < i ==> a[k] <= max
    invariant i == 0 ==> max == a[0]
    invariant sum <= i * max
  {
    sum := sum + a[i];
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>

