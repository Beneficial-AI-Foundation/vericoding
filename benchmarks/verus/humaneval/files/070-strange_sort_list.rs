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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}