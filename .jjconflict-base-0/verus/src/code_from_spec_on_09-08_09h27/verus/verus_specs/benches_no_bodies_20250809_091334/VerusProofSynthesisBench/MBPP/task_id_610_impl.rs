use vstd::prelude::*;

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    // pre-conditions-start
    requires
        list.len() > 0,
        0 < k <= list@.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
    // post-conditions-end
{
    let mut new_list = Vec::new();
    
    // Add elements before the k-th element (indices 0 to k-2)
    let mut i = 0;
    /* code modified by LLM (iteration 1): Added decreases clause to first while loop */
    while i < k - 1
        invariant
            0 <= i <= k - 1,
            new_list@ == list@.subrange(0, i as int),
        decreases k - 1 - i
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Skip the k-th element (index k-1) and add the rest (indices k to end)
    let mut j = k;
    /* code modified by LLM (iteration 1): Added decreases clause to second while loop */
    while j < list.len()
        invariant
            k <= j <= list.len(),
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, j as int)
            ),
        decreases list.len() - j
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!

fn main() {}