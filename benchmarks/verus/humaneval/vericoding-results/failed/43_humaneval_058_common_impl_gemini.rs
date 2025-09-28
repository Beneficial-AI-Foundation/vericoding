// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed invalid ensures clause from spec fn */
spec fn common_rec(l1: Seq<i32>, l2: Seq<i32>) -> Set<i32>
    decreases l1.len()
{
    if l1.len() == 0 {
        Set::empty()
    } else {
        let first = l1[0];
        let rest = l1.subrange(1, l1.len() as int);
        let result_rest = common_rec(rest, l2);
        if l2.contains(first) {
            result_rest.insert(first)
        } else {
            result_rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn common(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures 
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)) &&
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no change to code, fix is in helper function */
    common_rec(l1@, l2@)
}
// </vc-code>


}

fn main() {}