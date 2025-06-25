pub fn contains_consecutive_numbers(a: &[i32]) -> (result: bool)
    requires(a.len() > 0)
    ensures(result <==> (exists|i: usize| 0 <= i < a.len() - 1 && a[i] + 1 == a[i + 1]))
{
}