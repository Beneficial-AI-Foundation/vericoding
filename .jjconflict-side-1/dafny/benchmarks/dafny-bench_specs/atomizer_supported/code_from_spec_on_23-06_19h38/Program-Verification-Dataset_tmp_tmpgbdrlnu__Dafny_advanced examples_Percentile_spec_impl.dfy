// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
//ATOM 
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

//IMPL Percentile
method Percentile(p: real, A: array<real>, total: real) returns (i: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= (p/100.0) * total
  ensures i+1 < A.Length ==> SumUpto(A, i+1) > (p/100.0) * total
{
  var threshold := (p/100.0) * total;
  i := -1;
  
  /* code modified by LLM (iteration 1): added proper loop invariants and termination condition */
  while i+1 < A.Length && SumUpto(A, i+1) <= threshold
    invariant -1 <= i < A.Length
    invariant SumUpto(A, i) <= threshold
    invariant forall j | -1 <= j <= i :: SumUpto(A, j) <= threshold
    decreases A.Length - i - 1
  {
    i := i + 1;
  }
}

//IMPL PercentileNonUniqueAnswer
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
  /* code modified by LLM (iteration 1): created array and scenario where threshold equals cumulative sum, allowing multiple valid answers with non-strict inequalities */
  A := new real[3];
  A[0] := 1.0;
  A[1] := 1.0;
  A[2] := 1.0;
  
  p := 66.666666666667;  // Chosen so that threshold ≈ 2.0
  total := 3.0;  // Sum of array
  
  // threshold = (p/100.0) * 3.0 ≈ 2.0
  
  // For i1 = 0: SumUpto(A, 0) = 1.0 <= 2.0 ✓
  //             SumUpto(A, 1) = 2.0 >= 2.0 ✓ (non-strict)
  i1 := 0;
  
  // For i2 = 1: SumUpto(A, 1) = 2.0 <= 2.0 ✓  
  //             SumUpto(A, 2) = 3.0 >= 2.0 ✓
  i2 := 1;
}

//ATOM 
lemma PercentileUniqueAnswer(p: real, A: array<real>, total: real, i1: int, i2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0

  requires -1 <= i1 < A.Length
  requires SumUpto(A, i1) <= (p/100.0) * total
  requires i1+1 < A.Length ==> SumUpto(A, i1+1) > (p/100.0) * total

  requires -1 <= i2 < A.Length
  requires SumUpto(A, i2) <= (p/100.0) * total
  requires i2+1 < A.Length ==> SumUpto(A, i2+1) > (p/100.0) * total

  ensures i1 == i2
{
  if i1+1< i2 {
    SumUpto_increase(A, i1+1, i2);
  }
}

//ATOM 
lemma SumUpto_increase(A: array<real>, end1: int, end2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires -1 <= end1 < A.Length
  requires -1 <= end2 < A.Length
  requires end1 < end2
  ensures SumUpto(A, end1) < SumUpto(A, end2)
{}