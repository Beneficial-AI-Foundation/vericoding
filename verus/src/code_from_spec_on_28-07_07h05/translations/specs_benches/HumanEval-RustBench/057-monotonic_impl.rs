use vstd::prelude::*;

verus! {

fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
{
    /* code modified by LLM (iteration 4): Fixed invalid nat literal by using proper integer comparison */
    if l@.len() <= 1 {
        return true;
    }
    
    let mut is_non_decreasing = true;
    let mut is_non_increasing = true;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 4): Fixed loop bounds and invariants with proper type handling */
    while i < l.len() - 1
        invariant 
            0 <= i <= l@.len() - 1,
            l@.len() >= 2,
            is_non_decreasing <==> (forall|k: int, j: int| 0 <= k < j <= i ==> l@.index(k) <= l@.index(j)),
            is_non_increasing <==> (forall|k: int, j: int| 0 <= k < j <= i ==> l@.index(k) >= l@.index(j)),
    {
        /* code modified by LLM (iteration 4): Added bounds checking and proper indexing */
        if l[i] > l[i + 1] {
            is_non_decreasing = false;
        }
        if l[i] < l[i + 1] {
            is_non_increasing = false;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertion to help verification connect loop invariant to postcondition */
    assert(forall|k: int, j: int| 0 <= k < j < l@.len() ==> 
        (is_non_decreasing ==> l@.index(k) <= l@.index(j)) &&
        (is_non_increasing ==> l@.index(k) >= l@.index(j)));
    
    return is_non_decreasing || is_non_increasing;
}

}
fn main() {}