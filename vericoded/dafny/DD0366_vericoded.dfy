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
// No additional helpers needed
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
  A := new real[3];
  A[0] := 1.0;
  A[1] := 1.0;
  A[2] := 1.0;
  
  p := 100.0/3.0;  // 33.333...%
  total := 3.0;
  
  // At this point: (p/100.0) * total = (1/3) * 3.0 = 1.0
  
  i1 := 0;
  i2 := -1;
  
  // Verify the conditions:
  // SumUpto(A, 0) = A[0] = 1.0 = (p/100.0) * total ✓
  // SumUpto(A, -1) = 0.0 <= 1.0 = (p/100.0) * total ✓
  // SumUpto(A, 1) = A[0] + A[1] = 2.0 >= 1.0 = (p/100.0) * total ✓
  // SumUpto(A, 0) = 1.0 >= 1.0 = (p/100.0) * total ✓
  
  assert A[0] > 0.0 && A[1] > 0.0 && A[2] > 0.0;
  assert Sum(A) == SumUpto(A, 2) == 3.0;
  assert SumUpto(A, -1) == 0.0;
  assert SumUpto(A, 0) == 1.0;
  assert SumUpto(A, 1) == 2.0;
}
// </vc-code>

// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right