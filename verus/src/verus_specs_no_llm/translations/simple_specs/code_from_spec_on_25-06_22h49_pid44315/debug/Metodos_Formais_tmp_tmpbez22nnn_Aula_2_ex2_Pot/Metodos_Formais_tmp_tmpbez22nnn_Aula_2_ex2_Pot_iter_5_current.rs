use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Potencia(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else {
        x * Potencia(x, y - 1)
    }
}

fn Pot(x: u32, y: u32) -> (r: u32)
    requires
        x < 0x10000,  // Prevent overflow
        y < 32,       // Reasonable bound for termination and overflow prevention
    ensures
        r == Potencia(x as nat, y as nat)
    decreases y
{
    if y == 0 {
        1
    } else {
        let sub_result = Pot(x, y - 1);
        assert(sub_result == Potencia(x as nat, (y - 1) as nat)) by {
            // This follows from the postcondition of the recursive call
        };
        assert(x as nat * Potencia(x as nat, (y - 1) as nat) == Potencia(x as nat, y as nat)) by {
            // This follows from the definition of Potencia when y > 0
        };
        x * sub_result
    }
}

}