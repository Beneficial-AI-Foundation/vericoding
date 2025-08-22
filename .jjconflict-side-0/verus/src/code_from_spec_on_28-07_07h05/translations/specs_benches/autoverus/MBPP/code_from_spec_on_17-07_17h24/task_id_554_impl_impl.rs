use vstd::prelude::*;

fn main() {}

verus! {

/* code modified by LLM (iteration 4): Added helper lemma to prove filter property for subrange extension */
proof fn lemma_filter_subrange_push(arr: Seq<u32>, i: int, elem: u32)
    requires 
        0 <= i < arr.len(),
        arr[i] == elem,
    ensures
        arr.subrange(0, i + 1) == arr.subrange(0, i).push(elem),
        arr.subrange(0, i + 1).filter(|x: u32| x % 2 != 0) == 
            if elem % 2 != 0 { 
                arr.subrange(0, i).filter(|x: u32| x % 2 != 0).push(elem) 
            } else { 
                arr.subrange(0, i).filter(|x: u32| x % 2 != 0) 
            }
{
    assert(arr.subrange(0, i + 1) == arr.subrange(0, i).push(elem));
    
    if elem % 2 != 0 {
        assert(arr.subrange(0, i + 1).filter(|x: u32| x % 2 != 0) == 
               arr.subrange(0, i).filter(|x: u32| x % 2 != 0).push(elem));
    } else {
        assert(arr.subrange(0, i + 1).filter(|x: u32| x % 2 != 0) == 
               arr.subrange(0, i).filter(|x: u32| x % 2 != 0));
    }
}

//IMPL find_odd_numbers
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 4): Use helper lemma to prove invariant maintenance */
        let current_elem = arr[i];
        
        /* code modified by LLM (iteration 4): Apply lemma before branching */
        proof {
            lemma_filter_subrange_push(arr@, i as int, current_elem);
        }
        
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): Establish postcondition when loop exits */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!