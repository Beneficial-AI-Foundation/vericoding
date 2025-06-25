// ATOM 
spec fn C(n: nat) -> nat 
{
    if n == 0 { 1 } else { (4 * n - 2) * C((n-1) as nat) / (n + 1) }
}

// SPEC 

pub fn calcC(n: nat) -> (res: nat)
    ensures res == C(n)
{
}