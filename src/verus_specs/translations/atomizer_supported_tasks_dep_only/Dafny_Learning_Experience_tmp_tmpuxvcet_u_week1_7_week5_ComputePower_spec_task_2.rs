// ATOM 
pub fn power(n: nat) -> nat
{
    if n == 0 { 1 } else { 2 * power((n-1) as nat) }
}

// SPEC 
pub fn calc_power(n: nat) -> (p: nat)
    ensures p == 2*n
{
}

// SPEC 
pub fn compute_power(n: nat) -> (p: nat)
    ensures p == power(n)
{
}