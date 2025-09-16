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
{
    /* code modified by LLM (iteration 2): added decreases clause to fix compilation error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() == i,
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}