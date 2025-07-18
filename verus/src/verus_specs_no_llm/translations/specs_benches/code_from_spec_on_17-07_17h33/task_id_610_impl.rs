use vstd::prelude::*;

verus! {

//IMPL remove_kth_element
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
{
    return false;  // TODO: Remove this line and implement the function body
}
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
    /* code modified by LLM (iteration 1): moved requires/ensures clauses to correct position in function signature and implemented function body */
    let mut new_list = Vec::new();
    
    // Copy elements before the k-th element (indices 0 to k-1)
    let mut i = 0;
    while i < k - 1
        invariant
            i <= k - 1,
            new_list@ == list@.subrange(0, i as int),
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Copy elements after the k-th element (indices k onwards)
    let mut j = k;
    while j < list.len()
        invariant
            k <= j <= list.len(),
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