// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
// ATOM 
// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
spec fn SumUpto(A: &[f64], end: int) -> f64
    requires(-1 <= end < A.len())
{
    if end == -1 {
        0.0
    } else {
        A[end] + SumUpto(A, end-1)
    }
}

// ATOM 
spec fn Sum(A: &[f64]) -> f64 {
    SumUpto(A, A.len()-1)
}

// SPEC 
pub fn Percentile(p: f64, A: &[f64], total: f64) -> i32
    requires(
        forall|i: int| 0 <= i < A.len() ==> A[i] > 0.0,
        0.0 <= p <= 100.0,
        total == Sum(A),
        total > 0.0
    )
    ensures(|i: i32|
        -1 <= i < A.len() &&
        SumUpto(A, i) <= (p/100.0) * total &&
        (i+1 < A.len() ==> SumUpto(A, i+1) > (p/100.0) * total)
    )
{
}

// example showing that, with the original postcondition, the answer is non-unique!
// SPEC 
pub fn Percentile(p: f64, A: &[f64], total: f64) -> i32
    requires(
        forall|i: int| 0 <= i < A.len() ==> A[i] > 0.0,
        0.0 <= p <= 100.0,
        total == Sum(A),
        total > 0.0
    )
    ensures(|i: i32|
        -1 <= i < A.len() &&
        SumUpto(A, i) <= (p/100.0) * total &&
        (i+1 < A.len() ==> SumUpto(A, i+1) > (p/100.0) * total)
    )
{
}

// proof that, with the corrected postcondition, the answer is unique
// SPEC 
pub fn Percentile(p: f64, A: &[f64], total: f64) -> i32
    requires(
        forall|i: int| 0 <= i < A.len() ==> A[i] > 0.0,
        0.0 <= p <= 100.0,
        total == Sum(A),
        total > 0.0
    )
    ensures(|i: i32|
        -1 <= i < A.len() &&
        SumUpto(A, i) <= (p/100.0) * total &&
        (i+1 < A.len() ==> SumUpto(A, i+1) > (p/100.0) * total)
    )
{
}

// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right
// ATOM 
// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
spec fn SumUpto(A: &[f64], end: int) -> f64
    requires(-1 <= end < A.len())
{
    if end == -1 {
        0.0
    } else {
        A[end] + SumUpto(A, end-1)
    }
}