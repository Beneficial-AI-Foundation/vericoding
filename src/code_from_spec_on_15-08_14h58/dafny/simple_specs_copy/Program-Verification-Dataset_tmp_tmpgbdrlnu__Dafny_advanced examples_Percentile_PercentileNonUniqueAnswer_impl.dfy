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
 /* code modified by LLM (iteration 1): Fixed missing return value in then branch of if expression */
 if end == -1 then 0.0
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
    A := new real[4];
    A[0] := 1.0;
    A[1] := 1.0;
    A[2] := 1.0;
    A[3] := 1.0;
    
    p := 50.0;
    total := Sum(A);
    i1 := 1;
    /* code modified by LLM (iteration 2): Changed i2 to 0 to satisfy postconditions */
    i2 := 0;
    
    /* code modified by LLM (iteration 1): Added assertions to help Dafny verify the postconditions */
    // Help Dafny understand that total = 4.0
    assert A[0] + A[1] + A[2] + A[3] == 4.0;
    assert SumUpto(A, 3) == A[3] + SumUpto(A, 2);
    assert SumUpto(A, 2) == A[2] + SumUpto(A, 1);
    assert SumUpto(A, 1) == A[1] + SumUpto(A, 0);
    assert SumUpto(A, 0) == A[0] + SumUpto(A, -1);
    assert SumUpto(A, -1) == 0.0;
    assert SumUpto(A, 0) == 1.0;
    assert SumUpto(A, 1) == 2.0;
    assert SumUpto(A, 2) == 3.0;
    assert SumUpto(A, 3) == 4.0;
    assert total == 4.0;
    
    // Verify the percentile calculations: (p/100.0) * total = 0.5 * 4.0 = 2.0
    assert (p/100.0) * total == 2.0;
    
    // Verify conditions for i1 = 1
    assert SumUpto(A, i1) == SumUpto(A, 1) == 2.0;
    assert SumUpto(A, i1) <= 2.0;
    assert SumUpto(A, i1+1) == SumUpto(A, 2) == 3.0;
    assert SumUpto(A, i1+1) >= 2.0;
    
    /* code modified by LLM (iteration 2): Fixed verification for i2 = 0 */
    // Verify conditions for i2 = 0  
    assert SumUpto(A, i2) == SumUpto(A, 0) == 1.0;
    assert SumUpto(A, i2) <= 2.0;
    assert SumUpto(A, i2+1) == SumUpto(A, 1) == 2.0;
    assert SumUpto(A, i2+1) >= 2.0;
}