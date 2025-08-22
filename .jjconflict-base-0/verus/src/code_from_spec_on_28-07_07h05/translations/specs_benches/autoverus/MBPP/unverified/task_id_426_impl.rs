use vstd::prelude::*;

fn main() {}

verus! {

/* code modified by LLM (iteration 4): Added lemma to prove filter behavior when extending subrange with odd element */
proof fn lemma_filter_extend_odd(s: Seq<u32>, i: int, x: u32)
    requires
        0 <= i < s.len(),
        s[i] == x,
        x % 2 != 0,
    ensures
        s.subrange(0, i + 1).filter(|y: u32| y % 2 != 0) == 
        s.subrange(0, i).filter(|y: u32| y % 2 != 0).push(x),
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(x));
    
    // Prove that filter distributes over push for odd elements
    assert(sub_i_plus_1.filter(|y: u32| y % 2 != 0) == 
           sub_i.filter(|y: u32| y % 2 != 0).push(x)) by {
        assert(x % 2 != 0);
    }
}

/* code modified by LLM (iteration 4): Added lemma to prove filter behavior when extending subrange with even element */
proof fn lemma_filter_extend_even(s: Seq<u32>, i: int, x: u32)
    requires
        0 <= i < s.len(),
        s[i] == x,
        x % 2 == 0,
    ensures
        s.subrange(0, i + 1).filter(|y: u32| y % 2 != 0) == 
        s.subrange(0, i).filter(|y: u32| y % 2 != 0),
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(x));
    
    // Prove that filter ignores even elements
    assert(sub_i_plus_1.filter(|y: u32| y % 2 != 0) == 
           sub_i.filter(|y: u32| y % 2 != 0)) by {
        assert(x % 2 == 0);
    }
}

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            /* code modified by LLM (iteration 4): Use lemma to prove assertion for odd case */
            proof {
                lemma_filter_extend_odd(arr@, i as int, arr@[i as int]);
            }
            result.push(arr[i]);
        } else {
            /* code modified by LLM (iteration 4): Use lemma to prove assertion for even case */
            proof {
                lemma_filter_extend_even(arr@, i as int, arr@[i as int]);
            }
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): Added assertion to prove postcondition */
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    
    result
}

} // verus!