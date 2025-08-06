use vstd::prelude::*;

fn main() {}

verus! {

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut result = Vec::new();
    
    for i in 0..arr.len()
        invariant
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
    }
    
    result
}

} // verus!