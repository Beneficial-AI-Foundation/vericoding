pub fn deli(a: &mut [char], i: usize)
    requires(
        a.len() > 0,
        i < a.len(),
    )
    ensures(
        |result: (), old_a: &[char]| {
            forall(|j: usize| 0 <= j && j < i >>= a[j] == old_a[j]) &&
            forall(|j: usize| i <= j && j < a.len() - 1 >>= a[j] == old_a[j + 1]) &&
            a[a.len() - 1] == '.'
        }
    )
{
}

pub fn deli_checker()
{
}