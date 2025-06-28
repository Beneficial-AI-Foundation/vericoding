use builtin::*;
use builtin_macros::*;

verus! {

spec fn Stairs(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        1
    } else {
        Stairs(n - 1) + Stairs(n - 2)
    }
}

fn ClimbStairs(n: nat) -> (r: nat)
    ensures
        r == Stairs(n)
{
    if n == 0 {
        1
    } else if n == 1 {
        1
    } else {
        let mut prev2: nat = 1;  // Stairs(0)
        let mut prev1: nat = 1;  // Stairs(1)
        let mut i: nat = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                prev2 == Stairs(i - 2),
                prev1 == Stairs(i - 1),
        {
            let current = prev1 + prev2;
            
            // Prove that current equals Stairs(i)
            assert(current == prev1 + prev2);
            assert(prev1 == Stairs(i - 1));
            assert(prev2 == Stairs(i - 2));
            
            // Use the definition of Stairs to prove current == Stairs(i)
            assert(current == Stairs(i)) by {
                assert(i >= 2);
                assert(i != 0 && i != 1);
                // By definition of Stairs for i >= 2
                assert(Stairs(i) == Stairs(i - 1) + Stairs(i - 2));
            };
            
            prev2 = prev1;
            prev1 = current;
            i = i + 1;
        }
        
        // After the loop, i == n + 1, so prev1 == Stairs(n)
        assert(i == n + 1);
        assert(prev1 == Stairs(n));
        prev1
    }
}

fn main() {
}

}