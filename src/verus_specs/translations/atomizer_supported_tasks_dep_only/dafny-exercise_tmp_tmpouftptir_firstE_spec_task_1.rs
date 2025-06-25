pub fn firstE(a: &[char]) -> (x: i32)
    ensures(if a@.contains('e') then 0 <= x < a.len() && a[x as usize] == 'e' && forall|i: usize| 0 <= i < x ==> a[i] != 'e' else x == -1)
{
}