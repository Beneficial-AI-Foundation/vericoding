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
lemma SumMaxProperty(a: array<int>, N: int, sum: int, max: int)
  requires 0 <= N && a.Length == N
  requires forall k :: 0 <= k < N ==> 0 <= a[k]
  requires sum == ArraySum(a, 0, N)
  requires N > 0 ==> max == ArrayMax(a, 0, N)
  requires N == 0 ==> max >= 0
  ensures sum <= N * max
{
  if N == 0 {
    assert sum == 0;
    assert N * max == 0;
  } else {
    ArrayMaxProperty(a, 0, N);
    ArraySumBound(a, 0, N, max);
  }
}

function ArraySum(a: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= a.Length
  reads a
  decreases end - start
{
  if start == end then 0
  else a[start] + ArraySum(a, start + 1, end)
}

function ArrayMax(a: array<int>, start: int, end: int): int
  requires 0 <= start < end <= a.Length
  reads a
  decreases end - start
{
  if start == end - 1 then a[start]
  else
    var restMax := ArrayMax(a, start + 1, end);
    if a[start] >= restMax then a[start] else restMax
}

lemma ArraySumBound(a: array<int>, start: int, end: int, max: int)
  requires 0 <= start <= end <= a.Length
  requires forall k :: start <= k < end ==> 0 <= a[k] <= max
  ensures ArraySum(a, start, end) <= (end - start) * max
  decreases end - start
{
  if start == end {
  } else {
    ArraySumBound(a, start + 1, end, max);
  }
}

lemma ArrayMaxProperty(a: array<int>, start: int, end: int)
  requires 0 <= start < end <= a.Length
  ensures forall k :: start <= k < end ==> a[k] <= ArrayMax(a, start, end)
  decreases end - start
{
  if start == end - 1 {
  } else {
    ArrayMaxProperty(a, start + 1, end);
  }
}

lemma SumBoundAfterMaxUpdate(sum: int, i: int, oldMax: int, newMax: int)
  requires sum <= i * oldMax
  requires newMax >= oldMax
  ensures sum <= i * newMax
{
  assert i * oldMax <= i * newMax;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
// </vc-spec>
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
    invariant max >= 0
    invariant sum >= 0
    invariant forall k :: 0 <= k < i ==> a[k] <= max
    invariant sum <= i * max
    invariant i > 0 ==> (exists k :: 0 <= k < i && a[k] == max)
  {
    var oldMax := max;
    if a[i] > max {
      SumBoundAfterMaxUpdate(sum, i, max, a[i]);
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
    
    assert exists k :: 0 <= k < i && a[k] == max;
  }
}
// </vc-code>
