use vstd::prelude::*;

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    // post-conditions-start
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): fixed loop invariant maintenance */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
        
        /* code modified by LLM (iteration 3): added assertion to maintain invariant with correct Verus syntax */
        assert(arr@.subrange(0, i as int) == arr@.subrange(0, (i-1) as int).push(arr[(i-1) as int]));
        assert(arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0) == 
               arr@.subrange(0, (i-1) as int).filter(|x: u32| x % 2 == 0) + 
               (if arr[(i-1) as int] % 2 == 0 { seq![arr[(i-1) as int]] } else { seq![] }));
    }
    
    /* code modified by LLM (iteration 3): added assertion to help prove postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!

fn main() {}