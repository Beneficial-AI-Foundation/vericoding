use vstd::prelude::*;

verus! {

//IMPL filter_odd_numbers
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    /* code modified by LLM (iteration 3): Fixed loop invariant and added proper reasoning about filter operation */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 3): Added assertion to help prove invariant maintenance */
        assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr[i]));
        
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        
        /* code modified by LLM (iteration 3): Added assertion to prove invariant holds after iteration */
        assert(result@ == arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0));
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): Added assertion to establish postcondition from loop invariant */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!

fn main() {}