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

// Helper lemma to prove the key property we need
proof fn lemma_potencia_step(x: nat, i: nat)
    ensures
        x * Potencia(x, i) == Potencia(x, i + 1)
{
    // This follows directly from the definition of Potencia
    // when i + 1 > 0, Potencia(x, i + 1) = x * Potencia(x, (i + 1) - 1) = x * Potencia(x, i)
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
            // Before updating: result == Potencia(x, i)
            // We want: (result * x) == Potencia(x, i + 1)
            // This is: Potencia(x, i) * x == Potencia(x, i + 1)
            proof {
                lemma_potencia_step(x, i);
            }
            
            result = result * x;
            i = i + 1;
        }
        result
    }
}

}