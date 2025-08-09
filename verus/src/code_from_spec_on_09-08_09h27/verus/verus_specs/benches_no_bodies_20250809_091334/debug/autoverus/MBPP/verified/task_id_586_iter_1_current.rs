use vstd::prelude::*;

fn main() {
    let v = vec![1, 2, 3, 4, 5];
    let result = split_and_append(&v, 2);
    println!("Original: {:?}, Split at 2: {:?}", v, result);
}

verus! {

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    
    // First, append elements from index n to end
    let mut i = n;
    while i < list.len()
        invariant
            0 < n < list@.len(),
            n <= i <= list@.len(),
            new_list@ == list@.subrange(n as int, i as int),
    {
        new_list.push(list[i]);
        i += 1;
    }
    
    // Then, append elements from start to index n-1
    let mut j = 0;
    while j < n
        invariant
            0 < n < list@.len(),
            0 <= j <= n,
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, j as int)),
    {
        new_list.push(list[j]);
        j += 1;
    }
    
    new_list
}

} // verus!