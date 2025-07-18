use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 3): Fixed ghost type usage by using concrete len() instead of l@.len() as int */
fn monotonic(l: Vec<i32>) -> (ret: bool)
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
{
    /* code modified by LLM (iteration 3): Use concrete len() instead of ghost l@.len() as int */
    if l.len() <= 1 {
        return true;
    }
    
    let mut is_non_decreasing = true;
    let mut is_non_increasing = true;
    
    /* code modified by LLM (iteration 3): Fixed loop bounds and invariants to use concrete types properly */
    for i in 0..l.len() - 1
        invariant
            0 <= i <= l.len() - 1,
            is_non_decreasing <==> (forall|x: int, y: int| 0 <= x < y < i as int + 1 ==> l@.index(x) <= l@.index(y)),
            is_non_increasing <==> (forall|x: int, y: int| 0 <= x < y < i as int + 1 ==> l@.index(x) >= l@.index(y)),
    {
        if l[i] > l[i + 1] {
            is_non_decreasing = false;
        }
        if l[i] < l[i + 1] {
            is_non_increasing = false;
        }
    }
    
    /* code modified by LLM (iteration 3): Assertions to help verification connect loop results with postcondition */
    assert(is_non_decreasing <==> (forall|x: int, y: int| 0 <= x < y < l@.len() ==> l@.index(x) <= l@.index(y)));
    assert(is_non_increasing <==> (forall|x: int, y: int| 0 <= x < y < l@.len() ==> l@.index(x) >= l@.index(y)));
    
    return is_non_decreasing || is_non_increasing;
}

}
fn main() {}