pub fn MaxA(a: &[i32]) -> (m: i32)
    requires a.len() > 0
    ensures forall|i: usize| 0 <= i < a.len() ==> a[i] <= m
    ensures exists|i: usize| 0 <= i < a.len() && a[i] == m
{
}