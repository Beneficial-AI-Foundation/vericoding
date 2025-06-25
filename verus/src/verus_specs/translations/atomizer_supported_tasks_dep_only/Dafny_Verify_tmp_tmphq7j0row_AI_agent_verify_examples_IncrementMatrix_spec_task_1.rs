pub fn increment_matrix(a: &mut Array2<i32>)
    requires(true)
    ensures(forall|i: usize, j: usize| 0 <= i < old(a).length0() && 0 <= j < old(a).length1() ==> a[i][j] == old(a)[i][j] + 1)
{
}