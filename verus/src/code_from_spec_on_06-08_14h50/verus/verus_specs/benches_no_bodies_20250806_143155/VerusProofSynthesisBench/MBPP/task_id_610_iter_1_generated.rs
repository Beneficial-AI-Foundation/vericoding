use vstd::prelude::*;

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    // pre-conditions-start
    requires
        list.len() > 0,
        0 < k < list@.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
    // post-conditions-end
{
    let mut new_list = Vec::new();
    
    // Copy elements before the k-th element
    let mut i = 0;
    while i < k - 1
        invariant
            0 <= i <= k - 1,
            new_list@.len() == i,
            new_list@ == list@.subrange(0, i as int),
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Skip the k-th element and copy the rest
    let mut j = k;
    while j < list.len()
        invariant
            k <= j <= list.len(),
            new_list@.len() == (k - 1) + (j - k),
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, j as int)
            ),
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!

fn main() {}