use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
// Helper lemma to show stairs function properties
proof fn lemma_stairs_base_cases()
    ensures stairs(0) == 1,
            stairs(1) == 1,
{
}

proof fn lemma_stairs_recursive(n: nat)
    requires n >= 2
    ensures stairs(n) == stairs((n - 2) as nat) + stairs((n - 1) as nat)
{
}
// </vc-helpers>

// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// <vc-code>
{
    if n <= 1 {
        proof {
            lemma_stairs_base_cases();
        }
        1
    } else {
        let prev2 = climb_stairs(n - 2);
        let prev1 = climb_stairs(n - 1);
        proof {
            lemma_stairs_recursive(n as nat);
        }
        prev2 + prev1
    }
}
// </vc-code>

fn main() {
}

}