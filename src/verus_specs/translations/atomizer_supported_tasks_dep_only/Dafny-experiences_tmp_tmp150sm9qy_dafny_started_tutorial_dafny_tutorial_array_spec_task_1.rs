pub fn find_max(a: &[int]) -> (i: usize)
    requires(a.len() > 0)
    ensures(|result: usize| 0 <= result < a.len())
    ensures(|result: usize| forall|k: usize| 0 <= k < a.len() ==> a[k] <= a[result])
{
}