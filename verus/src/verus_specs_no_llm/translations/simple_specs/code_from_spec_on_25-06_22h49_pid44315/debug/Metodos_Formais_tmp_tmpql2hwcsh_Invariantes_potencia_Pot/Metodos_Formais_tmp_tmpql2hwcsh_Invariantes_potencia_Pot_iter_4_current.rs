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
            proof {
                // Prove that result * x == Potencia(x, i + 1)
                // This follows from the definition of Potencia
                assert(Potencia(x, i + 1) == x * Potencia(x, i)) by {
                    // The definition of Potencia directly gives us this equality
                    // since i + 1 > 0, so Potencia(x, i + 1) = x * Potencia(x, (i + 1) - 1) = x * Potencia(x, i)
                };
                assert(result == Potencia(x, i)); // from invariant
                assert(result * x == x * Potencia(x, i)); // commutativity
                assert(result * x == Potencia(x, i + 1)); // transitivity
            }
            result = result * x;
            i = i + 1;
        }
        result
    }
}

}