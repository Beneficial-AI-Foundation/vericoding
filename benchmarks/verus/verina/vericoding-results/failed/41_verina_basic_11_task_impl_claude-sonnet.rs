// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helpers since simple % operation is sufficient */
// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use nat directly without casting, return nat type */
    let result = n % 10;
    proof {
        assert(n % 10 < 10);
        assert(result == n % 10);
    }
    result
}
// </vc-code>

}
fn main() {}