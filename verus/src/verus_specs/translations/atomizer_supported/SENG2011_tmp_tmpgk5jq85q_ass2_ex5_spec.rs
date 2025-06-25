spec fn expo(x: int, n: nat) -> int
    requires n >= 0
{
    if n == 0 { 1 } else { x * expo(x, (n - 1) as nat) }
}

pub fn Expon23(n: nat)
    requires n >= 0
    ensures ((expo(2, 3 * n) - expo(3, n))) % 5 == 0
{
}

pub fn check() {
}