pub fn findMax(a: &mut Vec<i32>, n: i32) -> (r: i32)
    requires(
        a.len() > 0,
        0 < n <= a.len(),
    )
    ensures(|result: i32|
        0 <= result < n <= a.len() &&
        forall|k: i32| 0 <= k < n <= a.len() ==> a[result as int] >= a[k as int] &&
        a@ == old(a)@
    )
{
}