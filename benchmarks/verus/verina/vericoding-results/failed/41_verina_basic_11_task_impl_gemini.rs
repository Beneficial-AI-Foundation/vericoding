// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed compilation error by using the correct lemma name `lemma_mod_pos_bound`] */
    let result = n % 10;
    assert(result < 10) by {
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(n as int, 10);
    };
    result
}
// </vc-code>

}
fn main() {}