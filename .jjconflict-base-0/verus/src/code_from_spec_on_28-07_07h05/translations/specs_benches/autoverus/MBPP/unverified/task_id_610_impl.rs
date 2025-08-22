use vstd::prelude::*;
fn main() {}

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
    
    // Copy elements before index k-1 (0-based indexing)
    let mut i = 0;
    /* code modified by LLM (iteration 2): fixed invariant bounds and added bound check */
    while i < k - 1
        invariant
            0 <= i <= k - 1,
            k - 1 <= list.len(),
            new_list@.len() == i,
            new_list@ == list@.subrange(0, i as int),
        decreases (k - 1) - i,
    {
        /* code modified by LLM (iteration 2): added assertion to help verification */
        assert(i < list.len());
        new_list.push(list[i]);
        i += 1;
    }
    
    // Copy elements after index k-1 (skip the k-th element)
    let mut j = k;
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    while j < list.len()
        invariant
            k <= j <= list.len(),
            new_list@.len() == (k - 1) + (j - k),
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, j as int)
            ),
        decreases list.len() - j,
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!