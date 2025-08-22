use vstd::prelude::*;
fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    
    /* code modified by LLM (iteration 3): added precondition assertions to establish bounds */
    assert(k > 0);
    assert(k < list.len());
    assert(k - 1 < list.len());
    
    // Copy elements before the k-th element (indices 0 to k-2)
    let mut i = 0;
    /* code modified by LLM (iteration 3): simplified loop with corrected bounds */
    while i < k - 1
        invariant
            0 <= i <= k - 1,
            k - 1 < list.len(),
            i <= list.len(),
            new_list@ == list@.subrange(0, i as int),
        decreases k - 1 - i,
    {
        assert(i < k - 1);
        assert(i < list.len());
        new_list.push(list[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): added assertion to establish state after first loop */
    assert(i == k - 1);
    assert(k - 1 < list.len());
    
    // Copy elements after the k-th element (indices k to end)
    let mut j = k;
    /* code modified by LLM (iteration 3): corrected invariant with proper bounds */
    while j < list.len()
        invariant
            k <= j <= list.len(),
            k < list.len(),
            k - 1 < list.len(),
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, j as int)
            ),
        decreases list.len() - j,
    {
        assert(j < list.len());
        new_list.push(list[j]);
        j += 1;
    }
    
    /* code modified by LLM (iteration 3): final assertion to establish postcondition */
    assert(j == list.len());
    assert(new_list@ == list@.subrange(0, k - 1 as int).add(
        list@.subrange(k as int, list.len() as int)
    ));
    
    new_list
}

} // verus!