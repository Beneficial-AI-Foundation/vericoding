use vstd::prelude::*;

verus! {

fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
    // pre-conditions-end

    // post-conditions-start
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 3): fixed loop invariants and bounds, added proper type annotations */
    while i < l.len()
        invariant
            result.len() == i,
            i <= l.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == l[j] + 1,
        decreases l.len() - i
    {
        /* code modified by LLM (iteration 3): fixed syntax for chained comparison and added bounds check */
        assert(0 <= i as int && i as int < l.len());
        assert(l[i as int] + 1 <= i32::MAX) by {
            assert(forall|k: int| 0 <= k < l.len() ==> l[k] + 1 <= i32::MAX);
            assert(0 <= i as int && i as int < l.len());
        };
        result.push(l[i] + 1);
        i += 1;
    }
    
    result
}

}
fn main() {}