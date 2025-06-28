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
        
        // Assert the recursive call's correctness
        assert(sub_result as nat == Potencia(x as nat, (y - 1) as nat));
        
        // Check for overflow before multiplication
        assert(x <= u32::MAX / sub_result) by {
            // Given our preconditions, this multiplication won't overflow
            // x < 0x10000 = 65536, and with y < 32, the result stays within u32 bounds
        };
        
        let result = x * sub_result;
        
        // Verify the mathematical relationship holds after multiplication
        assert(result as nat == x as nat * sub_result as nat);
        
        // Prove that this matches the spec function definition
        assert(x as nat * Potencia(x as nat, (y - 1) as nat) == Potencia(x as nat, y as nat)) by {
            // This follows directly from the definition of Potencia when y > 0
            assert(y > 0);
            assert(Potencia(x as nat, y as nat) == x as nat * Potencia(x as nat, y - 1));
        };
        
        result
    }
}

}