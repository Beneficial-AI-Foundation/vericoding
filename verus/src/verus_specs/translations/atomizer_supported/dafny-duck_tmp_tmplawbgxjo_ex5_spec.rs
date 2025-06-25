pub fn expo(x: int, n: nat) -> int {
    if n == 0 { 1 } else { x * expo(x, n-1) }
}

pub fn Expon23(n: nat)
    requires(n >= 0)
    ensures(((expo(2, 3*n) - expo(3, n)) % (2+3)) == 0)
{
}