spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

pub fn is_product_even(a: &[int]) -> (result: bool)
    ensures(result <==> exists|i: int| 0 <= i < a.len() && is_even(a[i as usize]))
{
}