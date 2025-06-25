pub fn leq(a: &[i32], b: &[i32]) -> bool
    ensures(|result: bool| result <==> (a.len() <= b.len() && a[..] == b[..a.len()]) || (exists|k: usize| 0 <= k < a.len() && k < b.len() && a[..k] == b[..k] && a[k] < b[k]))
{
}