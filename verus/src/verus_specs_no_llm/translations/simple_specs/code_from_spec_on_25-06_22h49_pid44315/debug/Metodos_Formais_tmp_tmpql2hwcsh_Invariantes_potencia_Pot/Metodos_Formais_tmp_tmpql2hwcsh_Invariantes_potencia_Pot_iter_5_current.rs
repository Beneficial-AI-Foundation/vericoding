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
            
            proof {
                // After the updates, we need to verify the invariant holds
                // We have: old(result) == Potencia(x, old(i))
                // We updated: result = old(result) * x, i = old(i) + 1
                // We need to show: result == Potencia(x, i)
                // That is: old(result) * x == Potencia(x, old(i) + 1)
                
                // From the definition of Potencia:
                // Potencia(x, old(i) + 1) = x * Potencia(x, old(i))
                // And we know old(result) == Potencia(x, old(i))
                // So result = old(result) * x = Potencia(x, old(i)) * x = x * Potencia(x, old(i)) = Potencia(x, old(i) + 1)
                assert(Potencia(x, i) == Potencia(x, (i - 1) + 1));
                assert(Potencia(x, (i - 1) + 1) == x * Potencia(x, i - 1)) by {
                    // This follows from the definition of Potencia since (i - 1) + 1 > 0
                };
            }
        }
        result
    }
}

}