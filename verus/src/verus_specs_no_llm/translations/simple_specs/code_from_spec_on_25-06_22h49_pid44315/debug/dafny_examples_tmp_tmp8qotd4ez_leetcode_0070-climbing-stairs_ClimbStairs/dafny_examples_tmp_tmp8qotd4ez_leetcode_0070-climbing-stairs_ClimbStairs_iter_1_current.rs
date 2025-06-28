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
        let mut current = 1;
        let mut i = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                prev2 == Stairs((i - 2) as nat),
                prev1 == Stairs((i - 1) as nat),
        {
            current = prev1 + prev2;
            prev2 = prev1;
            prev1 = current;
            i = i + 1;
            
            assert(current == Stairs((i - 1) as nat));
        }
        
        return current;
    }
}

fn main() {
}

}