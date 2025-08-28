use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut new_list = Vec::new();
    
    let mut i: usize = 0;
    while i < k - 1
        invariant
            i <= k - 1,
            k > 0,
            k < list@.len(),
            new_list@.len() == i,
            new_list@ == list@.subrange(0, i as int),
        decreases k - 1 - i,
    {
        new_list.push(list[i]);
        i = i + 1;
    }
    
    let mut j: usize = k;
    while j < list.len()
        invariant
            j >= k,
            j <= list@.len(),
            k > 0,
            k < list@.len(),
            new_list@.len() == (k - 1) + (j - k),
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, j as int)
            ),
        decreases list@.len() - j,
    {
        new_list.push(list[j]);
        j = j + 1;
    }
    
    new_list
}
// </vc-code>

} // verus!

fn main() {}