pub fn tangent(r: &[i32], x: &[i32]) -> bool
    requires(
        forall|i: usize, j: usize| 0 <= i <= j < x.len() ==> x[i] <= x[j]
    )
    requires(
        forall|i: usize, j: usize| (0 <= i < r.len() && 0 <= j < x.len()) ==> (r[i] >= 0 && x[j] >= 0)
    )
    ensures(|b: bool|
        !b ==> forall|i: usize, j: usize| 0 <= i < r.len() && 0 <= j < x.len() ==> r[i] != x[j]
    )
    ensures(|b: bool|
        b ==> exists|i: usize, j: usize| 0 <= i < r.len() && 0 <= j < x.len() && r[i] == x[j]
    )
{
}