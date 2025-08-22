use vstd::prelude::*;

verus! {

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    // post-conditions-start
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
{
    let mut odd_numbers = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_numbers@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            odd_numbers.push(arr[i]);
        }
        i += 1;
    }
    
    odd_numbers
}

} // verus!

fn main() { }