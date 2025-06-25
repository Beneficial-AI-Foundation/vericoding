// ATOM 
spec fn calcSum(n: nat) -> nat 
{   
    n * (n - 1) / 2
}

// SPEC 
pub fn sum(n: nat) -> (s: nat)
    ensures s == calcSum(n + 1)
{
}