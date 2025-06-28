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
        Stairs((n - 1) as nat) + Stairs((n - 2) as nat)
    }
}

fn ClimbStairs(n: nat) -> (r: nat)
    ensures
        r == Stairs(n)
{
    if n == 0 {
        return 1;
    } else if n == 1 {
        return 1;
    } else {
        let mut prev2 = 1;  // Stairs(0)
        let mut prev1 = 1;  // Stairs(1)
        let mut i = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                prev2 == Stairs((i - 2) as nat),
                prev1 == Stairs((i - 1) as nat),
        {
            let current = prev1 + prev2;
            
            // Prove that current equals Stairs(i)
            assert(current == prev1 + prev2);
            assert(prev1 == Stairs((i - 1) as nat));
            assert(prev2 == Stairs((i - 2) as nat));
            assert(current == Stairs((i - 1) as nat) + Stairs((i - 2) as nat));
            assert(current == Stairs(i as nat)) by {
                assert(i >= 2);
                assert(Stairs(i as nat) == Stairs((i - 1) as nat) + Stairs((i - 2) as nat));
            };
            
            prev2 = prev1;
            prev1 = current;
            i = i + 1;
        }
        
        // After the loop, i == n + 1, so prev1 == Stairs(n)
        assert(i == n + 1);
        assert(prev1 == Stairs(n as nat));
        return prev1;
    }
}

fn main() {
}

}