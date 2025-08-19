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
    /* code modified by LLM (iteration 1): Create array with specific values to demonstrate non-unique percentile answer */
    A := new real[4];
    A[0] := 1.0;
    A[1] := 1.0;
    A[2] := 1.0;
    A[3] := 1.0;
    
    /* code modified by LLM (iteration 1): Set percentile to 50% */
    p := 50.0;
    
    /* code modified by LLM (iteration 1): Calculate total using Sum function */
    total := Sum(A);
    
    /* code modified by LLM (iteration 1): Select two different indices that both satisfy percentile conditions */
    i1 := 0;
    i2 := 1;
    
    /* code modified by LLM (iteration 1): Add detailed assertions to help Dafny verify step by step */
    assert A.Length == 4;
    assert A[0] == 1.0 && A[1] == 1.0 && A[2] == 1.0 && A[3] == 1.0;
    assert forall i | 0 <= i < A.Length :: A[i] == 1.0 > 0.0;
    
    assert 0.0 <= p <= 100.0;
    
    // Help Dafny understand SumUpto calculations
    assert SumUpto(A, -1) == 0.0;
    assert SumUpto(A, 0) == A[0] + SumUpto(A, -1) == 1.0 + 0.0 == 1.0;
    assert SumUpto(A, 1) == A[1] + SumUpto(A, 0) == 1.0 + 1.0 == 2.0;
    assert SumUpto(A, 2) == A[2] + SumUpto(A, 1) == 1.0 + 2.0 == 3.0;
    assert SumUpto(A, 3) == A[3] + SumUpto(A, 2) == 1.0 + 3.0 == 4.0;
    
    // Verify total calculation
    assert total == Sum(A) == SumUpto(A, A.Length-1) == SumUpto(A, 3) == 4.0;
    assert total > 0.0;
    
    // Calculate target percentile value
    assert (p/100.0) * total == (50.0/100.0) * 4.0 == 0.5 * 4.0 == 2.0;
    
    // Verify i1 = 0 satisfies conditions
    assert -1 <= i1 < A.Length;
    assert SumUpto(A, i1) == SumUpto(A, 0) == 1.0 <= 2.0;
    assert i1+1 == 1 < A.Length;
    assert SumUpto(A, i1+1) == SumUpto(A, 1) == 2.0 >= 2.0;
    
    // Verify i2 = 1 satisfies conditions  
    assert -1 <= i2 < A.Length;
    assert SumUpto(A, i2) == SumUpto(A, 1) == 2.0 <= 2.0;
    assert i2+1 == 2 < A.Length;
    assert SumUpto(A, i2+1) == SumUpto(A, 2) == 3.0 >= 2.0;
    
    // Verify i1 != i2
    assert i1 == 0 && i2 == 1;
    assert i1 != i2;
}