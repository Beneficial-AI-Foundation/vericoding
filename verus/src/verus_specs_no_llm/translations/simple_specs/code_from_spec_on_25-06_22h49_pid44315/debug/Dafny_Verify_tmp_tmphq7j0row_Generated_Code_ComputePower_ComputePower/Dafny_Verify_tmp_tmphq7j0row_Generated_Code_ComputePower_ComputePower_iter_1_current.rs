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
{
    if n == 0 {
        return 1;
    } else {
        let prev = ComputePower((n - 1) as nat);
        return 2 * prev;
    }
}

}

The implementation:


   - Base case: when n = 0, returns 1
   - Recursive case: computes Power(n-1) and multiplies by 2



The recursive implementation with the matching spec function allows Verus to verify that `ComputePower` correctly computes 2^n as specified by the `Power` function.