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
    
    // Add elements from index 0 to k-2 (inclusive)
    for i in 0..(k - 1)
        invariant
            new_list@ == list@.subrange(0, i as int),
    {
        new_list.push(list[i]);
    }
    
    // Add elements from index k to end
    for i in k..list.len()
        invariant
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, i as int)
            ),
    {
        new_list.push(list[i]);
    }
    
    new_list
}

} // verus!