use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    // pre-conditions-start
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut new_list = Vec::new();
    
    let mut i = n;
    /* code modified by LLM (iteration 2): added decreases clause for first loop */
    while i < list.len()
        invariant
            0 < n < list@.len(),
            i >= n,
            i <= list@.len(),
            new_list@ == list@.subrange(n as int, i as int),
        decreases list.len() - i,
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    let mut j = 0;
    /* code modified by LLM (iteration 2): added decreases clause for second loop */
    while j < n
        invariant
            0 < n < list@.len(),
            j <= n,
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, j as int)),
        decreases n - j,
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}
// </vc-code>

} // verus!

fn main() {}