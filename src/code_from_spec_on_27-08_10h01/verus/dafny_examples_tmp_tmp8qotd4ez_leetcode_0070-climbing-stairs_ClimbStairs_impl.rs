use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
proof fn stairs_properties(n: nat)
    ensures n >= 2 ==> stairs(n) == stairs((n - 2) as nat) + stairs((n - 1) as nat)
    ensures n <= 1 ==> stairs(n) == 1
    decreases n
{
}

proof fn stairs_monotonic(n: nat)
    ensures stairs(n) >= 1
    decreases n
{
    if n <= 1 {
    } else {
        stairs_monotonic((n - 2) as nat);
        stairs_monotonic((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n <= 1 {
        1
    } else {
        let mut prev2 = 1u32;
        let mut prev1 = 1u32;
        let mut i = 2u32;
        
        while i <= n
            invariant 
                2 <= i <= n + 1,
                prev2 == stairs((i - 2) as nat),
                prev1 == stairs((i - 1) as nat)
            decreases n - i
        {
            let current = prev2 + prev1;
            
            proof {
                assert(stairs(i as nat) == stairs((i - 2) as nat) + stairs((i - 1) as nat));
                assert(current == stairs(i as nat));
            }
            
            prev2 = prev1;
            prev1 = current;
            i = i + 1;
        }
        
        prev1
    }
}
// </vc-code>

fn main() {
}

}