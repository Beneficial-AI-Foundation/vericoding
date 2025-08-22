use vstd::prelude::*;
fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

//IMPL split_and_append
fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut result = Vec::new();
    
    // First, append elements from index n to the end
    let mut i = n;
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    while i < list.len()
        invariant
            n <= i <= list.len(),
            result@ == list@.subrange(n as int, i as int),
        decreases list.len() - i,
    {
        result.push(list[i]);
        i += 1;
    }
    
    // Then, append elements from the beginning to index n
    let mut j = 0;
    /* code modified by LLM (iteration 2): fixed loop invariant to handle bounds correctly and added precondition for array access */
    while j < n
        invariant
            0 <= j <= n,
            n < list.len(),
            result@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, j as int)),
        decreases n - j,
    {
        result.push(list[j]);
        j += 1;
    }
    
    result
}

} // verus!