pub fn M(N: int, a: &[int]) -> (sum: int, max: int)
    requires(
        0 <= N && a.len() == N && (forall|k: int| 0 <= k && k < N ==> 0 <= a[k as usize])
    )
    ensures(|result: (int, int)| 
        result.0 <= N * result.1
    )
{
}

pub fn Main()
{
}