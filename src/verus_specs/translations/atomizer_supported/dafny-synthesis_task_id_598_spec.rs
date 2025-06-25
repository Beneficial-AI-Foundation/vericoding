pub fn IsArmstrong(n: int) -> bool
    requires(100 <= n < 1000)
    ensures(|result: bool| result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10))))
{
}