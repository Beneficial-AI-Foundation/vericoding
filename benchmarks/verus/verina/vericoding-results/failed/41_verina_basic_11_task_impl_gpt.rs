// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove invalid nat suffix and prove modulo bound */
proof fn lemma_mod_lt_10(n: nat)
    ensures
        n % 10 < 10
{
    assert(10 > 0);
    assert(n % 10 < 10);
}
// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute modulo without nat literal suffix and use lemma */
    let r = n % 10;
    proof { lemma_mod_lt_10(n); }
    r
}
// </vc-code>

}
fn main() {}