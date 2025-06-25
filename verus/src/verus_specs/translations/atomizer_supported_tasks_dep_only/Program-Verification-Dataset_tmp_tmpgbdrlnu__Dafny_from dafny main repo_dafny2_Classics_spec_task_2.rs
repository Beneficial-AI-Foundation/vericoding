pub fn FIND(A: &mut [i32], N: i32, f: i32)
    requires(
        A.len() == N,
        0 <= f < N,
    )
    ensures(
        forall|p: i32, q: i32| 0 <= p <= f <= q < N ==> A[p as int] <= A[q as int]
    )
{
}