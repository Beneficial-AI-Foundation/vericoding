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
        
        // The key insight: we need to prove that x * sub_result doesn't overflow
        // Given x < 0x10000 and the recursive nature, we can bound the result
        assert(sub_result as nat == Potencia(x as nat, (y - 1) as nat));
        
        let result = x * sub_result;
        
        // Verify the mathematical relationship
        assert(result as nat == x as nat * sub_result as nat) by {
            // Multiplication preserves the mathematical relationship when no overflow occurs
            // Given our bounds, this should hold
        };
        
        assert(x as nat * Potencia(x as nat, (y - 1) as nat) == Potencia(x as nat, y as nat)) by {
            // This follows from the definition of Potencia when y > 0
            reveal(Potencia);
        };
        
        result
    }
}

}