use vstd::prelude::*;

fn main() {}

verus! {

//IMPL find_even_numbers
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut result = Vec::new();
    
    /* code modified by LLM (iteration 4): Fixed loop invariant to properly track the relationship between result and filtered elements */
    for i in 0..arr.len()
        invariant
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
            
            /* code modified by LLM (iteration 4): Added proper reasoning about filter distribution over sequence concatenation for even elements */
            assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int) + seq![arr@[i as int]]);
            assert(arr@[i as int] % 2 == 0);
            assert(seq![arr@[i as int]].filter(|x: u32| x % 2 == 0) == seq![arr@[i as int]]);
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0) + seq![arr@[i as int]].filter(|x: u32| x % 2 == 0));
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0) + seq![arr@[i as int]]);
        } else {
            /* code modified by LLM (iteration 4): Added proper reasoning about filter distribution over sequence concatenation for odd elements */
            assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int) + seq![arr@[i as int]]);
            assert(arr@[i as int] % 2 != 0);
            assert(seq![arr@[i as int]].filter(|x: u32| x % 2 == 0) == seq![]);
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0) + seq![arr@[i as int]].filter(|x: u32| x % 2 == 0));
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0));
        }
    }
    
    /* code modified by LLM (iteration 4): Added final assertion to establish postcondition */
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    
    result
}

} // verus!