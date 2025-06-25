pub fn SlopeSearch(a: &Array2<i32>, key: i32) -> (m: i32, n: i32)
    requires(
        forall|i: usize, j: usize, j_prime: usize| 
            0 <= i < a.len0() && 0 <= j < j_prime && j_prime < a.len1() ==> 
            a[i][j] <= a[i][j_prime]
    )
    requires(
        forall|i: usize, i_prime: usize, j: usize| 
            0 <= i < i_prime && i_prime < a.len0() && 0 <= j < a.len1() ==> 
            a[i][j] <= a[i_prime][j]
    )
    requires(
        exists|i: usize, j: usize| 
            0 <= i < a.len0() && 0 <= j < a.len1() && a[i][j] == key
    )
    ensures(
        0 <= m < a.len0() && 0 <= n < a.len1()
    )
    ensures(
        a[m as usize][n as usize] == key
    )
{
}