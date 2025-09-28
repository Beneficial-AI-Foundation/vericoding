// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 10000
}

spec fn valid_change(change: int) -> bool {
    0 <= change <= 999
}

spec fn correct_change(n: int) -> int
    recommends valid_input(n)
{
    (1000 - n % 1000) % 1000
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed lemma syntax by adding proper function indicator */
proof fn lemma_correct_change_properties(n: int)
    requires valid_input(n)
    ensures
        let remainder = n % 100;
        let change = if remainder == 0 { 0 } else { 100 - remainder };
        change == correct_change(n),
        0 <= change <= 99
{
    let remainder = n % 100;
    let change = if remainder == 0 { 0 } else { 100 - remainder };
    
    // Key insight: correct_change(n) = (1000 - n % 1000) % 1000
    // Since n <= 10000, we have n % 1000 = n % 100 when n < 1000
    // For general case: n % 1000 has same last two digits as n % 100
    
    assert(n % 1000 == (n / 100) % 10 * 100 + n % 100);
    
    if remainder == 0 {
        // n is multiple of 100
        assert(n % 100 == 0);
        assert((n % 1000) % 100 == 0);
        assert(correct_change(n) == (1000 - n % 1000) % 1000);
        assert(change == 0);
    } else {
        // n is not multiple of 100
        let n_mod_1000 = n % 1000;
        assert(n_mod_1000 % 100 == remainder);
        assert(1000 - n_mod_1000 == 1000 - (n_mod_1000 / 100) * 100 - remainder);
        assert((1000 - n_mod_1000) % 1000 == (1000 - remainder) % 1000);
        assert(1000 - remainder == (10 - remainder / 100) * 100 - remainder % 100);
        assert((1000 - remainder) % 1000 == 100 - remainder);
        assert(change == 100 - remainder);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (change: i8)
    requires valid_input(n as int)
    ensures 
        valid_change(change as int) &&
        change as int == correct_change(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added proof block with lemma call */
    let remainder = n % 100;
    
    proof {
        lemma_correct_change_properties(n as int);
    }
    
    if remainder == 0 {
        0
    } else {
        100 - remainder
    }
}
// </vc-code>


}

fn main() {}