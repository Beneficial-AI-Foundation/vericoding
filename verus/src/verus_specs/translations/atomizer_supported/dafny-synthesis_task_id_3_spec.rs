pub fn is_non_prime(n: int) -> (result: bool)
    requires(n >= 2)
    ensures(result <==> (exists|k: int| 2 <= k < n && n % k == 0))
{
}