spec fn F(n: nat) -> nat {
    if n <= 2 { n } else { F(n - 1) + F(n - 3) }
}

pub fn calcF(n: nat) -> (res: nat)
    ensures res == F(n)
{
}