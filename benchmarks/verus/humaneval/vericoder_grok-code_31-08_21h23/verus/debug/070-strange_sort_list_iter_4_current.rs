use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>

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
    let mut ret: Vec<i32> = s.clone();
    let len: usize = ret.len();
    for i in 0..len
        invariant
            s@.len() == ret@.len(),
    {
        let mut j: usize = i;
        while j >= 1
            invariant
                j <= i,
                s@.len() == ret@.len(),
        {
            if (ret[j-1] > ret[j]) {
                let tmp = ret[j-1];
                ret[j-1] = ret[j];
                ret[j] = tmp;
            }
            j = j - 1;
        }
    }
    ret
}
// </vc-code>

fn main() {}
}