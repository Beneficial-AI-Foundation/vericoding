// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn common(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures 
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)) &&
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed Set::empty() call to use spec mode */
    let ghost c = Set::empty();
    let mut result = Set::empty();
    let mut i = 0;
    
    while i < l1.len()
        invariant
            0 <= i <= l1.len(),
            result =~= c,
            forall|x: i32| c.contains(x) ==> l1@.contains(x) && l2@.contains(x),
            forall|x: i32| l1@.subrange(0, i as int).contains(x) && l2@.contains(x) ==> c.contains(x),
    {
        if l2@.contains(l1[i]) {
            result = result.insert(l1[i]);
        }
        i = i + 1;
    }
    
    proof {
        assert(l1@.subrange(0, l1.len() as int) =~= l1@);
        assert forall|x: i32| l1@.contains(x) && l2@.contains(x) implies result.contains(x) by {
            assert(result =~= c);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}