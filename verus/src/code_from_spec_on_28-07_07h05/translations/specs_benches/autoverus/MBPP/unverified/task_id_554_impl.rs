use vstd::prelude::*;

fn main() {}

verus! {

/* code modified by LLM (iteration 4): added helper lemma to prove subrange filter properties */
proof fn lemma_subrange_filter_extend_odd(arr: Seq<u32>, i: int, x: u32)
    requires
        0 <= i < arr.len(),
        arr[i] == x,
        x % 2 != 0,
    ensures
        arr.subrange(0, i + 1).filter(|y: u32| y % 2 != 0) == 
        arr.subrange(0, i).filter(|y: u32| y % 2 != 0).push(x),
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(x));
    
    // The filter of a sequence with an odd element pushed is the filter plus that element
    assert(sub_i_plus_1.filter(|y: u32| y % 2 != 0) == 
           sub_i.filter(|y: u32| y % 2 != 0).push(x)) by {
        assert(sub_i_plus_1.last() == x);
        assert(x % 2 != 0);
    }
}

/* code modified by LLM (iteration 4): added helper lemma for even case */
proof fn lemma_subrange_filter_extend_even(arr: Seq<u32>, i: int, x: u32)
    requires
        0 <= i < arr.len(),
        arr[i] == x,
        x % 2 == 0,
    ensures
        arr.subrange(0, i + 1).filter(|y: u32| y % 2 != 0) == 
        arr.subrange(0, i).filter(|y: u32| y % 2 != 0),
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(x));
    
    // The filter of a sequence with an even element pushed is unchanged
    assert(sub_i_plus_1.filter(|y: u32| y % 2 != 0) == 
           sub_i.filter(|y: u32| y % 2 != 0)) by {
        assert(sub_i_plus_1.last() == x);
        assert(x % 2 == 0);
    }
}

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): simplified loop with lemma calls */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
            /* code modified by LLM (iteration 4): use lemma to prove invariant maintenance */
            proof {
                lemma_subrange_filter_extend_odd(arr@, i as int, arr[i]);
            }
        } else {
            /* code modified by LLM (iteration 4): use lemma to prove invariant maintenance */
            proof {
                lemma_subrange_filter_extend_even(arr@, i as int, arr[i]);
            }
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): simplified final assertion */
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!