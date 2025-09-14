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


// example showing that, with the original postcondition, the answer is non-unique!

// <vc-helpers>
lemma SumUptoPositive(A: array<real>, end: int)
  requires 0 <= end < A.Length
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures SumUpto(A, end) > 0.0
{
  if end == 0 {
    // SumUpto(A,0) == A[0] by definition
    assert SumUpto(A, 0) == A[0];
    assert A[0] > 0.0;
  } else {
    SumUptoPositive(A, end-1);
    // unfold definition for end >= 1
    assert SumUpto(A, end) == A[end] + SumUpto(A, end-1);
    assert A[end] > 0.0;
    assert SumUpto(A, end-1) > 0.0;
    assert A[end] + SumUpto(A, end-1) > 0.0;
  }
}

lemma SumPositive(A: array<real>)
  requires A.Length > 0
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures Sum(A) > 0.0
{
  SumUptoPositive(A, A.Length-1);
  assert Sum(A) == SumUpto(A, A.Length-1);
}
// </vc-helpers>

// <vc-spec>
method PercentileNonUniqueAnswer() returns (p: real, A: array<real>, total: real, i1: int, i2: int)
  ensures forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures 0.0 <= p <= 100.0
  ensures total == Sum(A)
  ensures total > 0.0

  ensures -1 <= i1 < A.Length
  ensures SumUpto(A, i1) <= (p/100.0) * total
  ensures i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total

  ensures -1 <= i2 < A.Length
  ensures SumUpto(A, i2) <= (p/100.0) * total
  ensures i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total

  ensures i1 != i2
// </vc-spec>
// <vc-code>
{
  p := 100.0;
  A := new real[2];
  A[0] := 1.0;
  A[1] := 2.0;
  total := Sum(A);
  SumPositive(A);
  i1 := A.Length - 1;
  i2 := A.Length - 2;
  return;
}
// </vc-code>

// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right