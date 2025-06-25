pub fn TestArrayElements(a: &mut Vec<int>, j: nat)
    requires(
        0 <= j < a.len()
    )
    ensures(
        a[j] == 60,
        forall |k: int| 0 <= k < a.len() && k != j ==> a[k] == old(a)[k]
    )
{
}