pub fn IsPrime(m: int) -> (isPrime: bool)
    requires(m > 0)
    ensures(isPrime <==> (m > 1 && forall|j: int| 2 <= j < m ==> m % j != 0))
{
}