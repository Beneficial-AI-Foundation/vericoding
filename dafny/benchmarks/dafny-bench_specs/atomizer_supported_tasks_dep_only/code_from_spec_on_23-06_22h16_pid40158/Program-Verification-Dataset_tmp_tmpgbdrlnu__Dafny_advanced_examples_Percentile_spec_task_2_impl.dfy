//ATOM 
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

//ATOM 
function Sum(A: array<real>): real
  reads A
{
  SumUpto(A, A.Length-1)
}

//IMPL 
// example showing that, with the original postcondition, the answer is non-unique!
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
{
  /* code modified by LLM (iteration 1): Create array with values that allow multiple valid percentile positions */
  A := new real[6];
  A[0] := 1.0;
  A[1] := 1.0;
  A[2] := 1.0;
  A[3] := 1.0;
  A[4] := 1.0;
  A[5] := 1.0;
  
  p := 50.0;
  total := Sum(A);
  
  /* code modified by LLM (iteration 1): Set i1 and i2 to create non-unique percentile answer */
  i1 := 2;
  i2 := 1;
  
  /* code modified by LLM (iteration 1): Added assertions to help verification */
  assert total == 6.0;
  assert (p/100.0) * total == 3.0;
  assert SumUpto(A, 1) == 2.0;
  assert SumUpto(A, 2) == 3.0;
  assert SumUpto(A, 3) == 4.0;
  
  // Verify i1 = 2 satisfies conditions
  assert SumUpto(A, i1) == 3.0 <= 3.0;
  assert i1+1 < A.Length && SumUpto(A, i1+1) == 4.0 >= 3.0;
  
  // Verify i2 = 1 satisfies conditions  
  assert SumUpto(A, i2) == 2.0 <= 3.0;
  assert i2+1 < A.Length && SumUpto(A, i2+1) == 3.0 >= 3.0;
  
  assert i1 != i2;
}