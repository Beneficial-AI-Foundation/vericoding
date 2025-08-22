use vstd::prelude::*;

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    // post-conditions-start
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}