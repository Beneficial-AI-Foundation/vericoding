use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): Added decreases clause to prove loop termination and fixed invariant maintenance */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
            /* code modified by LLM (iteration 3): Fixed type mismatch by casting i to int and using proper sequence indexing */
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0) + seq![arr@[i as int]]);
        } else {
            /* code modified by LLM (iteration 3): Added assertion for the case when element is even */
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0));
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): Added final assertion to help prove postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!