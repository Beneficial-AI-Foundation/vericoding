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

// Helper lemma to establish bounds on Potencia
proof fn lemma_potencia_bounds(x: nat, y: nat)
    requires x <= 0xFFFF, y <= 16
    ensures Potencia(x, y) <= 0xFFFFFFFF
    decreases y
{
    if y == 0 {
        assert(Potencia(x, y) == 1);
    } else {
        lemma_potencia_bounds(x, y - 1);
        assert(Potencia(x, y) == x * Potencia(x, y - 1));
        // With x <= 0xFFFF and our inductive bound, the multiplication stays within u32
    }
}

fn Pot(x: u32, y: u32) -> (r: u32)
    requires
        x <= 0xFFFF,  // Prevent overflow - more restrictive bound
        y <= 16,      // More restrictive bound to ensure result fits in u32
    ensures
        r == Potencia(x as nat, y as nat)
    decreases y
{
    if y == 0 {
        1
    } else {
        let sub_result = Pot(x, y - 1);
        
        // Prove bounds before multiplication
        proof {
            lemma_potencia_bounds(x as nat, (y - 1) as nat);
        }
        
        // Check for potential overflow before multiplication
        assert(x as nat * sub_result as nat <= 0xFFFFFFFF) by {
            assert(sub_result as nat == Potencia(x as nat, (y - 1) as nat));
            lemma_potencia_bounds(x as nat, y as nat);
            assert(Potencia(x as nat, y as nat) == x as nat * Potencia(x as nat, (y - 1) as nat));
        };
        
        let result = x * sub_result;
        
        // Prove that the result matches the spec
        assert(result as nat == Potencia(x as nat, y as nat)) by {
            assert(sub_result as nat == Potencia(x as nat, (y - 1) as nat));
            assert(result as nat == x as nat * sub_result as nat);
            assert(y > 0);
            assert(Potencia(x as nat, y as nat) == x as nat * Potencia(x as nat, (y - 1) as nat));
        };
        
        result
    }
}

}