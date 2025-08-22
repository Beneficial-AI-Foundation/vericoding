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
    
    // Copy elements before index k-1 (since k is 1-indexed)
    let mut i = 0;
    while i < k - 1
        invariant
            0 <= i <= k - 1,
            new_list@ == list@.subrange(0, i as int),
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases k - 1 - i
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Skip element at index k-1 and copy the rest
    let mut j = k;
    while j < list.len()
        invariant
            k <= j <= list.len(),
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, j as int)
            ),
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases list.len() - j
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!