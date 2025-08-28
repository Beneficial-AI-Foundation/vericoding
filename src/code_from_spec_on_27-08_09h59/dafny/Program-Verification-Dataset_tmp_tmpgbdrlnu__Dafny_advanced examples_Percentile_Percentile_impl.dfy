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
lemma SumUptoIncreases(A: array<real>, i: int)
  requires forall j | 0 <= j < A.Length :: A[j] > 0.0
  requires 0 <= i < A.Length
  ensures SumUpto(A, i-1) < SumUpto(A, i)
{
  if i == 0 {
    assert SumUpto(A, -1) == 0.0;
    assert SumUpto(A, 0) == A[0] + SumUpto(A, -1) == A[0];
    assert A[0] > 0.0;
  } else {
    assert SumUpto(A, i) == A[i] + SumUpto(A, i-1);
    assert A[i] > 0.0;
  }
}

lemma SumUptoMonotonic(A: array<real>, i: int, j: int)
  requires forall k | 0 <= k < A.Length :: A[k] > 0.0
  requires -1 <= i <= j < A.Length
  requires i < j
  ensures SumUpto(A, i) < SumUpto(A, j)
{
  if i == j - 1 {
    SumUptoIncreases(A, j);
  } else {
    SumUptoMonotonic(A, i, j-1);
    SumUptoIncreases(A, j);
    assert SumUpto(A, i) < SumUpto(A, j-1) < SumUpto(A, j);
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
{
  var threshold := (p / 100.0) * total;
  i := -1;
  
  while i + 1 < A.Length && SumUpto(A, i + 1) <= threshold
    invariant -1 <= i < A.Length
    invariant SumUpto(A, i) <= threshold
    invariant forall j | -1 <= j <= i :: SumUpto(A, j) <= threshold
  {
    i := i + 1;
  }
}
// </vc-code>

// example showing that, with the original postcondition, the answer is non-unique!


// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right