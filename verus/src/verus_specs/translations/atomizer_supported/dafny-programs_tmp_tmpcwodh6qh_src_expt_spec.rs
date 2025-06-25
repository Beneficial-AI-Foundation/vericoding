// ATOM 
spec fn Expt(b: int, n: nat) -> int
    recommends n >= 0
{
    if n == 0 { 1 } else { b * Expt(b, (n - 1) as nat) }
}

// SPEC 

pub fn expt(b: int, n: nat) -> (res: int)
    ensures(res == Expt(b, n))
{
}

proof fn distributive(x: int, a: nat, b: nat)
    ensures(Expt(x, a) * Expt(x, b) == Expt(x, a + b))
{
}