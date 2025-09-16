// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)

    ensures
        s@.len() == ret@.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added loop invariant to ensure output length matches input. */
{
    let mut ret = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            ret@.len() == i,
            i <= s@.len(),
        decreases s@.len() - i
    {
        ret.push(s[i]);
        i += 1;
    }
    ret
}
// </vc-code>

}
fn main() {}