pub fn get_even(a: &mut [usize])
    requires(true)
    ensures(forall|i: int| 0 <= i < a.len() ==> a[i] % 2 == 0)
{
}