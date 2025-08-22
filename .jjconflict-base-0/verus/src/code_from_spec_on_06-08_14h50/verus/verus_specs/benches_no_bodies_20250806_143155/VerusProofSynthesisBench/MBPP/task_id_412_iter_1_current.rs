use vstd::prelude::*;

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    // post-conditions-start
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    
    for i in 0..arr.len()
        invariant
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0)
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
    }
    
    result
}

} // verus!

fn main() {}