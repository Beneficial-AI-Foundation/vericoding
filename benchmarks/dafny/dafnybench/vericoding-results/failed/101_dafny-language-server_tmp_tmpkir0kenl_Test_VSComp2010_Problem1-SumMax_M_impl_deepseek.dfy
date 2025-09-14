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
lemma MaxProperty(N: int, a: array<int>, max: int, i: int)
  requires 0 <= i <= N && a.Length == N
  requires (forall k :: 0 <= k && k < i ==> a[k] <= max)
  requires (exists k :: 0 <= k && k < i && a[k] == max) || i == 0
  ensures (forall k :: 0 <= k && k < i ==> a[k] <= N * max)
{
}

lemma SumProperty(N: int, a: array<int>, sum: int, max: int, i: int)
  requires 0 <= i <= N && a.Length == N
  requires (forall k :: 0 <= k && k < i ==> a[k] <= max)
  requires sum == (sum j | 0 <= j < i :: a[j])
  ensures sum <= i * max
{
  if i > 0 {
    SumProperty(N, a, sum - a[i-1], max, i-1);
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
  sum := 0;
  max := 0;
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant sum == (sum j | 0 <= j < i :: a[j])
    invariant max >= 0
    invariant (forall k :: 0 <= k && k < i ==> a[k] <= max)
    invariant (exists k :: 0 <= k && k < i && a[k] == max) || i == 0
    invariant sum <= i * max
  {
    if max < a[i] {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
    
    SumProperty(N, a, sum, max, i);
    MaxProperty(N, a, max, i);
  }
}
// </vc-code>

