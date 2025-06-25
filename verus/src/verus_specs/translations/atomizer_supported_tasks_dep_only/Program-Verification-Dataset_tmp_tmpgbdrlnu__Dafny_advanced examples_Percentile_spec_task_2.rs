use vstd::prelude::*;

verus! {

// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
// ATOM 
// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
spec fn SumUpto(A: &[f64], end: int) -> f64
    recommends -1 <= end < A.len()
{
    if end == -1 {
        0.0
    } else {
        A[end as usize] + SumUpto(A, end-1)
    }
}

// ATOM 
spec fn Sum(A: &[f64]) -> f64
{
    SumUpto(A, A.len() as int - 1)
}

//ATOM_PLACEHOLDER_Percentile

// example showing that, with the original postcondition, the answer is non-unique!
// SPEC 

// example showing that, with the original postcondition, the answer is non-unique!
pub fn PercentileNonUniqueAnswer() -> (p: f64, A: Vec<f64>, total: f64, i1: int, i2: int)
    ensures forall|i: int| 0 <= i < A@.len() ==> A@[i] > 0.0,
    ensures 0.0 <= p <= 100.0,
    ensures total == Sum(&A@),
    ensures total > 0.0,
    ensures -1 <= i1 < A@.len(),
    ensures SumUpto(&A@, i1) <= (p/100.0) * total,
    ensures i1+1 < A@.len() ==> SumUpto(&A@, i1+1) >= (p/100.0) * total,
    ensures -1 <= i2 < A@.len(),
    ensures SumUpto(&A@, i2) <= (p/100.0) * total,
    ensures i2+1 < A@.len() ==> SumUpto(&A@, i2+1) >= (p/100.0) * total,
    ensures i1 != i2,
{
}

}