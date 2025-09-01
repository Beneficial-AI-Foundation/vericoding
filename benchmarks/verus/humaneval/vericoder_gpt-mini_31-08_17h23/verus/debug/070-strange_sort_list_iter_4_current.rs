use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    // impl-start
    let mut res: Vec<i32> = Vec::new();
    let n: nat = s.len();
    let mut i: nat = 0;
    while i < n {
        invariant(i <= n);
        invariant(res@.len() == i);
        let x: i32 = s.index(i);
        res.push(x);
        i = i + 1;
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}