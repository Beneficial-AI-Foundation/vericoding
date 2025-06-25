pub fn SlopeSearch(a: &Array2<i32>, key: i32) -> (m: i32, n: i32)
    requires(
        forall|i: usize, j: usize, j_prime: usize| 
            0 <= i < a.len0() && 0 <= j < j_prime < a.len1() ==> a[i][j] <= a[i][j_prime]
    )
    requires(
        forall|i: usize, i_prime: usize, j: usize| 
            0 <= i < i_prime < a.len0() && 0 <= j < a.len1() ==> a[i][j] <= a[i_prime][j]
    )
    requires(
        exists|i: usize, j: usize| 
            0 <= i < a.len0() && 0 <= j < a.len1() && a[i][j] == key
    )
    ensures(|result: (i32, i32)| 
        0 <= result.0 < a.len0() && 0 <= result.1 < a.len1()
    )
    ensures(|result: (i32, i32)| 
        a[result.0 as usize][result.1 as usize] == key
    )
{
}