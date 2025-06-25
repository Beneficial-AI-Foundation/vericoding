pub fn swap<T>(a: &mut [T], i: usize, j: usize)
    requires(
        i < a.len() && j < a.len()
    )
    ensures(
        |result: ()| {
            a[i] == old(a)[j] &&
            a[j] == old(a)[i] &&
            (forall|m: usize| m < a.len() && m != i && m != j ==> a[m] == old(a)[m]) &&
            a@ == old(a)@
        }
    )
{
}