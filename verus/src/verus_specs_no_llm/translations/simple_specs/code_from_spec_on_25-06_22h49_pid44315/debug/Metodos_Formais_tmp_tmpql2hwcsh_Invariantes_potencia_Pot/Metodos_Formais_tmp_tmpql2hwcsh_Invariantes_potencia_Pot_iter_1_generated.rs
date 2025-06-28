use builtin::*;
use builtin_macros::*;

verus! {

// Spec function defining exponentiation
spec fn Potencia(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else {
        x * Potencia(x, y - 1)
    }
}

fn main() {
}

fn Pot(x: nat, y: nat) -> (r: nat)
    ensures
        r == Potencia(x, y)
{
    if y == 0 {
        1
    } else {
        let mut result: nat = 1;
        let mut i: nat = 0;
        while i < y
            invariant
                result == Potencia(x, i),
                i <= y,
        {
            result = result * x;
            i = i + 1;
        }
        result
    }
}

}

The implementation includes:




The key insight is using a loop invariant to prove that the iterative computation matches the recursive specification, allowing Verus to verify that the final result equals `Potencia(x, y)`.