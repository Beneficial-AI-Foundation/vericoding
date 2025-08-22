use vstd::prelude::*;

verus! {

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
{
    let mut new_list = Vec::new();
    
    // First, append elements from position n to the end
    let mut i = n;
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    while i < list.len()
        invariant
            n <= i <= list.len(),
            new_list@ == list@.subrange(n as int, i as int),
        decreases list.len() - i,
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Then, append elements from the beginning to position n
    let mut j = 0;
    /* code modified by LLM (iteration 2): fixed invariant bounds and added proper bounds checks */
    while j < n
        invariant
            0 <= j <= n,
            n < list@.len(),
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, j as int)),
        decreases n - j,
    {
        /* code modified by LLM (iteration 2): added bounds assertion before array access */
        assert(j < n);
        assert(n < list@.len());
        assert(j < list@.len());
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!

fn main() {}