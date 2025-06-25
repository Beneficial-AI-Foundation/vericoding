//ATOM

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
 if end == -1 then
  0.0
 else
  A[end] + SumUpto(A, end-1)
}


//IMPL PercentileNonUniqueAnswer

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
    /* code modified by LLM (iteration 1): Created array with specific values to demonstrate non-unique percentile answers */
    A := new real[4];
    A[0] := 1.0;
    A[1] := 1.0;
    A[2] := 1.0;
    A[3] := 1.0;
    
    /* code modified by LLM (iteration 1): Set percentile and calculate total */
    p := 25.0;
    total := Sum(A);
    
    /* code modified by LLM (iteration 1): Added assertion to help verify total calculation */
    assert total == 4.0;
    
    /* code modified by LLM (iteration 1): Set indices to demonstrate non-uniqueness */
    i1 := -1;
    i2 := 0;
    
    /* code modified by LLM (iteration 1): Added assertions to verify the percentile conditions */
    var threshold := (p/100.0) * total;
    assert threshold == 1.0;
    
    // Verify conditions for i1 = -1
    assert SumUpto(A, i1) == 0.0;
    assert SumUpto(A, i1) <= threshold;
    assert i1 + 1 == 0;
    assert i1 + 1 < A.Length;
    assert SumUpto(A, i1 + 1) == 1.0;
    assert SumUpto(A, i1 + 1) >= threshold;
    
    // Verify conditions for i2 = 0  
    assert SumUpto(A, i2) == 1.0;
    assert SumUpto(A, i2) <= threshold;
    assert i2 + 1 == 1;
    assert i2 + 1 < A.Length;
    assert SumUpto(A, i2 + 1) == 2.0;
    assert SumUpto(A, i2 + 1) >= threshold;
    
    /* code modified by LLM (iteration 1): Final verification that i1 != i2 */
    assert i1 != i2;
}