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
  
  /* code modified by LLM (iteration 4): Added proper loop invariant to ensure postcondition */
  while i + 1 < A.Length && SumUpto(A, i+1) <= threshold
    invariant -1 <= i < A.Length
    invariant SumUpto(A, i) <= threshold
    invariant i + 1 < A.Length ==> (SumUpto(A, i+1) <= threshold <==> SumUpto(A, i+1) <= threshold)
  {
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Added assertion to help prove postcondition */
  assert i + 1 >= A.Length || SumUpto(A, i+1) > threshold;
}

//IMPL NonUniqueAnswer
method NonUniqueAnswer(p: real, A: array<real>, total: real) returns (i: int)
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
  
  /* code modified by LLM (iteration 4): Added proper loop invariant to ensure postcondition */
  while i + 1 < A.Length && SumUpto(A, i+1) <= threshold
    invariant -1 <= i < A.Length
    invariant SumUpto(A, i) <= threshold
    invariant i + 1 < A.Length ==> (SumUpto(A, i+1) <= threshold <==> SumUpto(A, i+1) <= threshold)
  {
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Added assertion to help prove postcondition */
  assert i + 1 >= A.Length || SumUpto(A, i+1) > threshold;
}

//IMPL UniqueAnswer
method UniqueAnswer(p: real, A: array<real>, total: real) returns (i: int)
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
  
  /* code modified by LLM (iteration 4): Added proper loop invariant to ensure postcondition */
  while i + 1 < A.Length && SumUpto(A, i+1) <= threshold
    invariant -1 <= i < A.Length
    invariant SumUpto(A, i) <= threshold
    invariant i + 1 < A.Length ==> (SumUpto(A, i+1) <= threshold <==> SumUpto(A, i+1) <= threshold)
  {
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Added assertion to help prove postcondition */
  assert i + 1 >= A.Length || SumUpto(A, i+1) > threshold;
}

//ATOM 
lemma SumUptoIncreases(A: array<real>, i: int, j: int)
  requires forall k | 0 <= k < A.Length :: A[k] > 0.0
  requires -1 <= i < j < A.Length
  ensures SumUpto(A, i) < SumUpto(A, j)
{
  if i == j - 1 {
    // Base case: SumUpto(A, j) = A[j] + SumUpto(A, j-1) = A[j] + SumUpto(A, i)
    // Since A[j] > 0.0, we have SumUpto(A, j) > SumUpto(A, i)
  } else {
    // Inductive case: use transitivity
    SumUptoIncreases(A, i, j-1);
    SumUptoIncreases(A, j-1, j);
  }
}