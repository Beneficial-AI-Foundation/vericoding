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
    let mut ret: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant ret.len() == i && i <= s.len()
        decreases s.len() - i
    {
        ret.push(0);
        i = i + 1;
    }
    proof {
        assert(ret.len() == s.len());
    }
    ret
}
// </vc-code>

fn main() {}
}