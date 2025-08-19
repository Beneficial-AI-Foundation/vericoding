function Sum(A: array<real>): real
 reads A
{
 SumUpto(A, A.Length-1)
}


//ATOM
// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
function SumUpto(A: array<real>, end: int): real
 requires -1 <= end < A.Length
 reads A
{
 /* code modified by LLM (iteration 1): Fixed missing return value in then branch */
 if end == -1 then
  0.0
 else
  A[end] + SumUpto(A, end-1)
}

/* code modified by LLM (iteration 3): Removed reads clause from lemma as lemmas cannot have reads clauses */
lemma SumUptoLemma(A: array<real>, end: int)
  requires -1 <= end < A.Length
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures end >= 0 ==> SumUpto(A, end) == A[end] + SumUpto(A, end-1)
  ensures end == -1 ==> SumUpto(A, end) == 0.0
{
  // The lemma body is empty as Dafny can prove this from the function definition
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
  /* code modified by LLM (iteration 2): Added array initialization and assignments */
  A := new real[3];
  A[0] := 2.0;
  A[1] := 2.0;
  A[2] := 2.0;
  
  p := 50.0;
  total := Sum(A);
  
  /* code modified by LLM (iteration 2): Added helper lemma calls and step-by-step verification */
  SumUptoLemma(A, -1);
  SumUptoLemma(A, 0);
  SumUptoLemma(A, 1);
  SumUptoLemma(A, 2);
  
  assert SumUpto(A, -1) == 0.0;
  assert SumUpto(A, 0) == A[0] + SumUpto(A, -1) == 2.0 + 0.0 == 2.0;
  assert SumUpto(A, 1) == A[1] + SumUpto(A, 0) == 2.0 + 2.0 == 4.0;
  assert SumUpto(A, 2) == A[2] + SumUpto(A, 1) == 2.0 + 4.0 == 6.0;
  assert total == SumUpto(A, 2) == 6.0;
  
  i1 := 0;
  i2 := 1;
  
  /* code modified by LLM (iteration 2): Added detailed assertions for verification */
  assert (p/100.0) * total == (50.0/100.0) * 6.0 == 0.5 * 6.0 == 3.0;
  assert SumUpto(A, i1) == SumUpto(A, 0) == 2.0;
  assert SumUpto(A, i2) == SumUpto(A, 1) == 4.0;
  assert 2.0 <= 3.0;
  assert 4.0 > 3.0;
}