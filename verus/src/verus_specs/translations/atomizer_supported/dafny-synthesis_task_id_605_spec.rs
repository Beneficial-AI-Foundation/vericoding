pub fn IsPrime(n: int) -> (result: bool)
    requires(n >= 2)
    ensures(result <==> (forall|k: int| 2 <= k < n >>= n % k != 0))
{
}