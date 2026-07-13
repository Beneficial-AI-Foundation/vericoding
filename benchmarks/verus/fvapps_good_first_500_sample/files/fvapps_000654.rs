// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_naughty(x: nat, a: nat, d: nat) -> bool {
    x % a == 0 || 
    x % (a + d) == 0 || 
    x % (a + 2*d) == 0 || 
    x % (a + 3*d) == 0 || 
    x % (a + 4*d) == 0
}

fn count_santa_gifts(n: nat, m: nat, a: nat, d: nat) -> (result: nat)
    requires 
        n > 0,
        m > 0,
        a > 0,
        d > 0,
        n <= m,
    ensures
        result >= 0,
        result <= m - n + 1,
        /* Core property: result counts houses in range [n,m] that are not naughty */
        forall|x: nat| n <= x <= m && !is_naughty(x, a, d) ==> result > 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // Test cases would go here:
    // count_santa_gifts(2, 20, 2, 1) should return 5
    // count_santa_gifts(1, 5, 2, 1) should return 1  
    // count_santa_gifts(3, 7, 2, 1) should return 1
}