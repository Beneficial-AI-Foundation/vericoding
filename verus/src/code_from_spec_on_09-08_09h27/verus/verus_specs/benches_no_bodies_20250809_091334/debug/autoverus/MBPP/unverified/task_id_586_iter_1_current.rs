use vstd::prelude::*;
fn main() {}

verus! {

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    
    // First, append elements from position n to end
    let mut i = n;
    while i < list.len()
        invariant
            n <= i <= list.len(),
            new_list@ == list@.subrange(n as int, i as int),
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Then, append elements from start to position n
    let mut j = 0;
    while j < n
        invariant
            0 <= j <= n,
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, j as int)),
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!