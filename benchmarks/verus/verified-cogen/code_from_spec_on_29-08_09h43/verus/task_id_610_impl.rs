use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    
    let mut i = 0;
    /* code modified by LLM (iteration 3): fixed bounds check and invariant for first loop */
    while i < k - 1 && i < list.len()
        invariant
            0 <= i <= k - 1,
            i <= list.len(),
            new_list@ == list@.subrange(0, i as int),
        decreases k - 1 - i
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    let mut j = k;
    /* code modified by LLM (iteration 3): added bounds check for second loop */
    while j < list.len()
        invariant
            k <= j <= list.len(),
            new_list@ == list@.subrange(0, (k - 1) as int).add(
                list@.subrange(k as int, j as int)
            ),
        decreases list.len() - j
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}
// </vc-code>

} // verus!

fn main() {}