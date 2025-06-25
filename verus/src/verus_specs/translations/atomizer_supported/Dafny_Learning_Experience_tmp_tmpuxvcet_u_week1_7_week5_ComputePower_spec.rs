// ATOM 
pub fn Power(n: nat) -> nat
{
    if n == 0 { 1 } else { 2 * Power((n-1) as nat) }
}

// SPEC 

pub fn CalcPower(n: nat) -> (p: nat)
    ensures p == 2*n
{
}

// SPEC 

pub fn ComputePower(n: nat) -> (p: nat)
    ensures p == Power(n)
{
}