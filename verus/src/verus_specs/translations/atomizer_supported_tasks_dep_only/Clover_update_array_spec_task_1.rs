pub fn update_elements(a: &mut [i32])
    requires(a.len() >= 8)
    ensures(old(a)[4] + 3 == a[4])
    ensures(a[7] == 516)
    ensures(forall|i: usize| 0 <= i < a.len() ==> i != 7 && i != 4 ==> a[i] == old(a)[i])
{
}