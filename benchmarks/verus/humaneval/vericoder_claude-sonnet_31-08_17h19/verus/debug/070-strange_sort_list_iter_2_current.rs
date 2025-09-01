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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() == i,
        decreases s.len() - i,
    {
        result.push(s[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}