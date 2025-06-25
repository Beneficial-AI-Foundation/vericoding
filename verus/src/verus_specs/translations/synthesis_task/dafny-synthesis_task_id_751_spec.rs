pub fn is_min_heap(a: &[int]) -> (result: bool)
    requires(
        true
    )
    ensures(|result: bool|
        result ==> forall|i: int| 0 <= i < a.len() / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.len() || a[i] <= a[2*i + 2])
    )
    ensures(|result: bool|
        !result ==> exists|i: int| 0 <= i < a.len() / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.len() && a[i] > a[2*i + 2]))
    )
{
}