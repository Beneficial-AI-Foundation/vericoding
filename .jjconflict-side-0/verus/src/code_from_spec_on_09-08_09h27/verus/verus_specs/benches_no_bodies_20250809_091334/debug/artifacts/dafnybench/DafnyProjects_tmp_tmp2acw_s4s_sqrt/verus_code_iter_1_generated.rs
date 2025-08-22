use vstd::prelude::*;

verus! {
    // Note: Verus doesn't have a built-in real type like Dafny
    // This translation uses i32 for executable code, but specifications use int
    // In practice, you'd need to work with rational numbers or a different approach for reals
    
    fn sqrt(x: i32) -> (r: i32)
        requires x >= 0,
        ensures r * r == x && r >= 0
    {
        let mut i = 0;
        while i * i < x
            invariant 0 <= i && i * i <= x
        {
            i = i + 1;
        }
        if i * i == x {
            i
        } else {
            // No perfect square root exists for this x
            // This function can only succeed for perfect squares
            panic!("No perfect square root")
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
        // This follows from the axioms of integer arithmetic in Verus
        // The proof is automatic given the requires clause
    }

    proof fn monotonicSquare(x: int, y: int)
        requires 0 < x < y,
        ensures 0 < x * x < y * y
    {
        // We can use the monotonicMult lemma
        monotonicMult(x, x, y);  // proves x * x < x * y
        monotonicMult(y, x, y);  // proves x * y < y * y
        
        // By transitivity: x * x < x * y < y * y, so x * x < y * y
        // x * x > 0 follows from x > 0
    }
}

fn main() {}