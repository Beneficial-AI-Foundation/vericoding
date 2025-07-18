use vstd::prelude::*;

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    /* code modified by LLM (iteration 3): Fixed loop invariant and added proof assertions */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 3): Added proof assertion to help verification */
        assert(arr@.subrange(0, i as int + 1) == arr@.subrange(0, i as int).push(arr[i as int]));
        
        if arr[i] < 0 {
            result.push(arr[i]);
            
            /* code modified by LLM (iteration 3): Added proof assertion about filter property */
            assert(arr@.subrange(0, i as int + 1).filter(|x: i32| x < 0) == 
                   arr@.subrange(0, i as int).filter(|x: i32| x < 0).push(arr[i as int]));
        } else {
            /* code modified by LLM (iteration 3): Added proof assertion for non-negative case */
            assert(arr@.subrange(0, i as int + 1).filter(|x: i32| x < 0) == 
                   arr@.subrange(0, i as int).filter(|x: i32| x < 0));
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): Added final proof assertion */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!

fn main() {}