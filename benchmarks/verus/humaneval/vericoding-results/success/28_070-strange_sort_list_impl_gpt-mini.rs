// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): clone Vec<i32> helper */
fn clone_vec_i32(s: &Vec<i32>) -> Vec<i32> { s.clone() }
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)

    ensures
        s@.len() == ret@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): copy elements using runtime indexing */
    let mut ret: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            ret.len() == i,
        decreases s.len() - i
    {
        ret.push(s[i]);
        i = i + 1;
    }
    ret
}
// </vc-code>

}
fn main() {}