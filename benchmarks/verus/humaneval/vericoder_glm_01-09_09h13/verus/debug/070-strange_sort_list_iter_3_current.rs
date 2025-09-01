use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
#[verifier(pure)]
fn abs_key(x: &i32) -> i32 {
    (*x).abs()
}
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut v = s.clone();
    v.sort_by_key(abs_key);
    v
}
// </vc-code>

fn main() {}
}