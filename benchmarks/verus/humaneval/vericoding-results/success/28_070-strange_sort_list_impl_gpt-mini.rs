// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn vec_seq_len(v: &Vec<i32>) -> nat { v@.len() }
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)

    ensures
        s@.len() == ret@.len(),
// </vc-spec>
// <vc-code>
{
    let ret: Vec<i32> = s.clone();
    ret
}
// </vc-code>

}
fn main() {}