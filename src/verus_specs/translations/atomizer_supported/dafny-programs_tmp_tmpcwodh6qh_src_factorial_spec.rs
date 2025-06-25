// ATOM 
spec fn fact(n: nat) -> nat 
    ensures |result: nat| result >= 1
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// SPEC 
pub fn factorial(n: nat) -> (res: nat)
    ensures res == fact(n)
{
}