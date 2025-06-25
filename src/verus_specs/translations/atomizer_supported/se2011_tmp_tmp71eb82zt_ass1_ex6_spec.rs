pub fn ceiling7(n: nat) -> (k: nat)
    requires(n >= 0)
    ensures(k == n - (n % 7))
{
}

pub fn test7()
{
}