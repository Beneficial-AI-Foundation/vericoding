use vstd::prelude::*;

fn main() {}

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): fixed loop invariant and added proof annotations */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
        
        /* code modified by LLM (iteration 3): wrapped ghost code in proof block to fix int type usage */
        proof {
            assert(arr@.subrange(0, (i-1) as int + 1) == arr@.subrange(0, i as int));
            
            let old_subrange = arr@.subrange(0, (i-1) as int);
            let new_subrange = arr@.subrange(0, i as int);
            assert(new_subrange == old_subrange.push(arr@[i-1]));
            
            if arr[i-1] % 2 == 0 {
                assert(new_subrange.filter(|x: u32| x % 2 == 0) == 
                       old_subrange.filter(|x: u32| x % 2 == 0).push(arr@[i-1]));
            } else {
                assert(new_subrange.filter(|x: u32| x % 2 == 0) == 
                       old_subrange.filter(|x: u32| x % 2 == 0));
            }
        }
    }
    
    /* code modified by LLM (iteration 3): wrapped final proof in proof block */
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    result
}

} // verus!