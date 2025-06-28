use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define what Power means
spec fn Power(n: nat) -> nat {
    2 * n
}

fn CalcPower(n: nat) -> (p: nat)
    ensures p == 2 * n
{
    2 * n
}

fn ComputePower(n: nat) -> (p: nat)
    ensures 
        p == 2 * n,
        p == Power(n)
{
    2 * n
}

}