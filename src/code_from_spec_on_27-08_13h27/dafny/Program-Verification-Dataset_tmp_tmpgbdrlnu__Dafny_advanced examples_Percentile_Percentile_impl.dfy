// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
function SumUpto(A: array<real>, end: int): real
  requires -1 <= end < A.Length
  reads A
{
  if end == -1 then
    0.0
  else
    A[end] + SumUpto(A, end-1)
}

function Sum(A: array<real>): real
  reads A
{
  SumUpto(A, A.Length-1)
}

// <vc-helpers>
lemma SumUptoMonotonic(A: array<real>, i: int, j: int)
  requires -1 <= i <= j < A.Length
  requires forall k | 0 <= k < A.Length :: A[k] > 0.0
  ensures SumUpto(A, i) <= SumUpto(A, j)
{
  if i == j {
    assert SumUpto(A, i) == SumUpto(A, j);
  } else if i == -1 {
    assert SumUpto(A, i) == 0.0;
    assert SumUpto(A, j) > 0.0;
  } else {
    assert SumUpto(A, j) == SumUpto(A, j-1) + A[j];
    SumUptoMonotonic(A, i, j-1);
    assert SumUpto(A, i) <= SumUpto(A, j-1);
    assert SumUpto(A, j-1) < SumUpto(A, j);
  }
}

lemma SumUptoStrictlyIncreasing(A: array<real>, i: int)
  requires -1 <= i < A.Length
  requires forall k | 0 <= k < A.Length :: A[k] > 0.0
  ensures i + 1 < A.Length ==> SumUpto(A, i) < SumUpto(A, i + 1)
{
  if i + 1 < A.Length {
    assert SumUpto(A, i + 1) == SumUpto(A, i) + A[i + 1];
    assert A[i + 1] > 0.0;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Percentile(p: real, A: array<real>, total: real) returns (i: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= (p/100.0) * total
  ensures i+1 < A.Length ==> SumUpto(A, i+1) > (p/100.0) * total
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputePercentile(p: real, A: array<real>, total: real) returns (i: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= (p/100.0) * total
  ensures i+1 < A.Length ==> SumUpto(A, i+1) > (p/100.0) * total
{
  var target := (p / 100.0) * total;
  i := -1;
  var currentSum := 0.0;
  
  while i + 1 < A.Length && currentSum < target
    invariant -1 <= i < A.Length
    invariant currentSum == SumUpto(A, i)
    invariant currentSum <= target
    invariant i + 1 < A.Length ==> SumUpto(A, i + 1) > currentSum
  {
    i := i + 1;
    currentSum := currentSum + A[i];
  }
}
// </vc-code>

// example showing that, with the original postcondition, the answer is non-unique!


// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right