pub fn max_array(a: &[i32]) -> (max: i32)
    requires(
        a.len() > 0
    )
    ensures(|max: i32|
        forall|i: usize| 0 <= i < a.len() ==> a[i] <= max &&
        exists|i: usize| 0 <= i < a.len() && a[i] == max
    )
{
}