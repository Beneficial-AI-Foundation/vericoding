use vstd::prelude::*;

fn main() {
}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        if arr[i] < 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    result
}

} // verus!