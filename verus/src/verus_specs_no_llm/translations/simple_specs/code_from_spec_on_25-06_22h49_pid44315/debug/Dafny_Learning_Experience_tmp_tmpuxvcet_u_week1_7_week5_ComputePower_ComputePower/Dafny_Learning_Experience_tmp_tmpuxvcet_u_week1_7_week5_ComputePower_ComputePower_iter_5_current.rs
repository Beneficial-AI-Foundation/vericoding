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
    (2 * n) as nat
}

fn ComputePower(n: nat) -> (p: nat)
    ensures 
        p == 2 * n,
        p == Power(n)
{
    let result = (2 * n) as nat;
    assert(result == Power(n)) by {
        assert(result == 2 * n);
        assert(Power(n) == 2 * n);
    };
    result
}

}