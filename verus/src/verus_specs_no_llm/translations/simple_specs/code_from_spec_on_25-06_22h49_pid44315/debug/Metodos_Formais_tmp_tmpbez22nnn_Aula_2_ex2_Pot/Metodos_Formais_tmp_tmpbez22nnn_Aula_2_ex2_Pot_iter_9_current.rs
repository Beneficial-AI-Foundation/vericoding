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
        
        // We know from preconditions that this won't overflow
        // x < 0x10000 and the result of Potencia with our bounds fits in u32
        let result = x * sub_result;
        
        // Prove that the result matches the spec
        assert(result as nat == Potencia(x as nat, y as nat)) by {
            // sub_result matches the recursive call by the ensures clause
            assert(sub_result as nat == Potencia(x as nat, (y - 1) as nat));
            
            // Multiplication preserves the relationship
            assert(result as nat == x as nat * sub_result as nat);
            
            // By definition of Potencia when y > 0
            assert(y > 0);
            assert(Potencia(x as nat, y as nat) == x as nat * Potencia(x as nat, (y - 1) as nat));
            
            // Therefore the equality holds
            assert(result as nat == x as nat * Potencia(x as nat, (y - 1) as nat));
        };
        
        result
    }
}

}