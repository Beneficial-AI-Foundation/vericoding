use vstd::prelude::*;

verus! {

// ATOM 
spec fn Power(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * Power((n - 1) as nat) }
}

// SPEC 
pub fn ComputePower(N: int) -> (y: nat)
    requires(N >= 0)
    ensures(y == Power(N as nat))
{
    
}

}