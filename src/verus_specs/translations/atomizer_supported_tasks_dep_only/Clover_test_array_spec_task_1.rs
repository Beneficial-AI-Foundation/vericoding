pub fn TestArrayElements(a: &mut [i32], j: usize)
    requires(
        j < a.len()
    )
    ensures(
        a[j as int] == 60
    )
    ensures(
        forall|k: int| 0 <= k < a.len() && k != j ==> a[k] == old(a)[k]
    )
{
}