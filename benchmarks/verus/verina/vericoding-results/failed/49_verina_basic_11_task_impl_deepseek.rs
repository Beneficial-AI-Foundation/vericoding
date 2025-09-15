// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Remove helper function and add proper lemma */
proof fn lemma_div_mod_connection(a: int, d: int)
    requires
        d != 0,
    ensures
        a % d >= 0,
        a % d < d,
{
    // Built-in verus knowledge about modulo properties
}
// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Use proper casting and calling of lemma */
{
    proof {
        lemma_div_mod_connection(n as int, 10);
    }
    let result = (n % 10) as nat;
    result
}
// </vc-code>

}
fn main() {}