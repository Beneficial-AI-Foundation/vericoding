use vstd::prelude::*;

fn main() {
}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < arr.len()
        invariant
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
            i <= arr.len(),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    result
}

} // verus!