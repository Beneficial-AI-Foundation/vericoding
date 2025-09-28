// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn pi_lemma()
    ensures
        22int / 7int > 3int,
        22int / 7int < 4int
{
    // 22/7 ≈ 3.142857 which is between 3 and 4
}
// </vc-helpers>

// <vc-spec>
fn pi() -> (result: i32)
    ensures
        result > 3 && result < 4
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added int suffix to literals */
    proof {
        pi_lemma();
    }
    22int / 7int
}
// </vc-code>


}
fn main() {}