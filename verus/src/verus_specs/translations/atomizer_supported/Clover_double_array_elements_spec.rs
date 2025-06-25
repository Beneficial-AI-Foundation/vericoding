pub fn double_array_elements(s: &mut [i32])
    requires(true)
    ensures(forall|i: usize| 0 <= i < s.len() ==> s[i] == 2 * old(s)[i])
{
}