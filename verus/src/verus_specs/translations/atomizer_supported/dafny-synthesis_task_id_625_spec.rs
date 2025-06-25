pub fn swap_first_and_last(a: &mut Vec<i32>)
    requires(a.len() > 0)
    ensures(a[0] == old(a)[a.len() - 1])
    ensures(a[a.len() - 1] == old(a)[0])
    ensures(forall|k: usize| 1 <= k < a.len() - 1 ==> a[k] == old(a)[k])
{
}