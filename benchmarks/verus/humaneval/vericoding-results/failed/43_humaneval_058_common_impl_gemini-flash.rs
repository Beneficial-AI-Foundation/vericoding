// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed the use of `Set::empty()` to use the `empty()` method directly on the `Set` type instead of calling it on a variable. */
#[allow(unused_mut)]
fn common_internal(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)),
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
{
    let mut common_set: Set<i32> = Set::<i32>::empty();
    let mut i = 0;
    while i < l1.len()
        invariant
            0 <= i,
            i <= l1.len(),
            (forall|val: i32| common_set.contains(val) ==> (l1@.contains(val) && l2@.contains(val)))
        decreases l1.len() - i
    {
        let val = *l1.get(i as usize).unwrap();
        if l2@.contains(val) {
            common_set = common_set.insert(val);
        }
        i = i + 1;
    }
    common_set
}
// </vc-helpers>

// <vc-spec>
fn common(l1: &Vec<i32>, l2: &Vec<i32>) -> (c: Set<i32>)
    ensures 
        (forall|i: i32| c.contains(i) ==> l1@.contains(i) && l2@.contains(i)) &&
        (forall|i: i32| l1@.contains(i) && l2@.contains(i) ==> c.contains(i))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Calling the helper function common_internal to retrieve the common elements. */
{
    common_internal(l1, l2)
}
// </vc-code>


}

fn main() {}