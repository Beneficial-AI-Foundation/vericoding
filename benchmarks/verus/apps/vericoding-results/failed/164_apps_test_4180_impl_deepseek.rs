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
proof fn lemma_mod_properties(a: int, b: int)
    requires
        b > 0,
    ensures
        a % b >= 0,
        a % b < b,
{
}

proof fn lemma_mod_complement(n: int)
    requires
        1 <= n <= 10000,
    ensures
        (1000 - n % 1000) % 1000 >= 0,
        (1000 - n % 1000) % 1000 <= 999,
        (1000 - n % 1000) % 1000 == correct_change(n),
{
    lemma_mod_properties(n, 1000);
    lemma_mod_properties(1000 - n % 1000, 1000);
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
/* code modified by LLM (iteration 5): avoid nat/int conversion in exec code */
{
    proof {
        lemma_mod_complement(n as int);
    }
    let change_val = (1000 - (n as int) % 1000) % 1000;
    assert(0 <= change_val <= 999);
    let change_i8 = change_val as i8;
    change_i8
}
// </vc-code>


}

fn main() {}