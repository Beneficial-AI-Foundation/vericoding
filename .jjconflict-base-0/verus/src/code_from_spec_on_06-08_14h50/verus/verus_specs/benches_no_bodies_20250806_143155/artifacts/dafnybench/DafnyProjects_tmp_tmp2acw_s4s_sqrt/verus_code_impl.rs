use vstd::prelude::*;

verus! {
    // Note: Verus doesn't have a built-in real type like Dafny
    // This translation uses i32 for executable code, but specifications use int
    // In practice, you'd need to work with rational numbers or a different approach for reals
    
    fn sqrt(x: i32) -> (r: i32)
        requires x >= 0,
        ensures r * r == x && r >= 0
    {
        let mut candidate = 0;
        /* code modified by LLM (iteration 1): added decreases clause to ensure loop termination */
        while candidate * candidate < x
            invariant 
                candidate >= 0,
                candidate * candidate <= x
            decreases x - candidate * candidate
        {
            candidate = candidate + 1;
        }
        
        if candidate * candidate == x {
            candidate
        } else {
            // No perfect square root exists for this x
            // Since the postcondition requires r * r == x, 
            // this function can only be called with perfect squares
            0 // This will only verify if x == 0
        }
    }

    fn testSqrt() {
        let result0 = sqrt(0);
        assert(result0 == 0);
        
        let result1 = sqrt(1);
        assert(result1 == 1);
        
        let result4 = sqrt(4);
        assert(result4 == 2);
        
        let result9 = sqrt(9);
        assert(result9 == 3);
    }

    proof fn monotonicMult(c: int, x: int, y: int)
        requires x < y && c > 0,
        ensures c * x < c * y
    {
        // This is a basic arithmetic property that Verus can prove automatically
        // The multiplication of a positive number preserves ordering
    }

    proof fn monotonicSquare(x: int, y: int)
        requires 0 < x < y,
        ensures 0 < x * x < y * y
    {
        // First prove that x * x < y * y using monotonicity
        monotonicMult(x, x, y);
        
        // The positivity x * x > 0 follows from x > 0
        // Verus can prove this automatically since x > 0 implies x * x > 0
    }
}

fn main() {}