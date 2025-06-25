// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
// ATOM 
// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
spec fn SumUpto(A: &[f64], end: int) -> f64
    recommends(-1 <= end < A.len())
{
    if end == -1 {
        0.0
    } else {
        A[end] + SumUpto(A, end-1)
    }
}

// ATOM 
spec fn Sum(A: &[f64]) -> f64
{
    SumUpto(A, A.len() as int - 1)
}

// SPEC 
pub fn Percentile(p: f64, A: &[f64], total: f64) -> i: int
    requires(forall|i: int| 0 <= i < A.len() ==> A[i] > 0.0)
    requires(0.0 <= p <= 100.0)
    requires(total == Sum(A))
    requires(total > 0.0)
    ensures(-1 <= i < A.len())
    ensures(SumUpto(A, i) <= (p/100.0) * total)
    ensures(i+1 < A.len() ==> SumUpto(A, i+1) > (p/100.0) * total)
{
}

// example showing that, with the original postcondition, the answer is non-unique!
// SPEC 
// example showing that, with the original postcondition, the answer is non-unique!
pub fn PercentileNonUniqueAnswer() -> (p: f64, A: Vec<f64>, total: f64, i1: int, i2: int)
    ensures(forall|i: int| 0 <= i < A.len() ==> A[i] > 0.0)
    ensures(0.0 <= p <= 100.0)
    ensures(total == Sum(&A))
    ensures(total > 0.0)
    ensures(-1 <= i1 < A.len())
    ensures(SumUpto(&A, i1) <= (p/100.0) * total)
    ensures(i1+1 < A.len() ==> SumUpto(&A, i1+1) >= (p/100.0) * total)
    ensures(-1 <= i2 < A.len())
    ensures(SumUpto(&A, i2) <= (p/100.0) * total)
    ensures(i2+1 < A.len() ==> SumUpto(&A, i2+1) >= (p/100.0) * total)
    ensures(i1 != i2)
{
}

// proof that, with the corrected postcondition, the answer is unique
// ATOM 
// proof that, with the corrected postcondition, the answer is unique
proof fn PercentileUniqueAnswer(p: f64, A: &[f64], total: f64, i1: int, i2: int)
    requires(forall|i: int| 0 <= i < A.len() ==> A[i] > 0.0)
    requires(0.0 <= p <= 100.0)
    requires(total == Sum(A))
    requires(total > 0.0)
    requires(-1 <= i1 < A.len())
    requires(SumUpto(A, i1) <= (p/100.0) * total)
    requires(i1+1 < A.len() ==> SumUpto(A, i1+1) > (p/100.0) * total)
    requires(-1 <= i2 < A.len())
    requires(SumUpto(A, i2) <= (p/100.0) * total)
    requires(i2+1 < A.len() ==> SumUpto(A, i2+1) > (p/100.0) * total)
    ensures(i1 == i2)
{
}

// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right
// ATOM 
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right
proof fn SumUpto_increase(A: &[f64], end1: int, end2: int)
    requires(forall|i: int| 0 <= i < A.len() ==> A[i] > 0.0)
    requires(-1 <= end1 < A.len())
    requires(-1 <= end2 < A.len())
    requires(end1 < end2)
    ensures(SumUpto(A, end1) < SumUpto(A, end2))
{
}