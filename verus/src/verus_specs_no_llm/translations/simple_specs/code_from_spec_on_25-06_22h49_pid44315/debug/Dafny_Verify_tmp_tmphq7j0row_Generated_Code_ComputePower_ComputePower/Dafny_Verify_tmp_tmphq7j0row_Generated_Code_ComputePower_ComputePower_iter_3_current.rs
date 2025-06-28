use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to define what Power means
spec fn Power(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * Power((n - 1) as nat)
    }
}

fn main() {
}

fn ComputePower(n: nat) -> (p: nat)
    ensures
        p == Power(n)
    decreases n
{
    if n == 0 {
        1
    } else {
        // We know n > 0 here, so n - 1 is safe
        assert(n >= 1);
        let prev = ComputePower(n - 1);
        2 * prev
    }
}

}