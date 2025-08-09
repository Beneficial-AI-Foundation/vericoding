use vstd::prelude::*;
fn main() {
    println!("Program executed successfully");
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
    let mut result = Vec::new();
    
    // Add elements before the k-th element (indices 0 to k-2)
    let mut i = 0;
    while i < k - 1
        invariant
            0 <= i <= k - 1,
            result.len() == i,
            result@ == list@.subrange(0, i as int),
    {
        result.push(list[i]);
        i += 1;
    }
    
    // Add elements after the k-th element (indices k to end)
    let mut j = k;
    while j < list.len()
        invariant
            k <= j <= list.len(),
            result.len() == (k - 1) + (j - k),
            result@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, j as int)
            ),
    {
        result.push(list[j]);
        j += 1;
    }
    
    result
}

} // verus!