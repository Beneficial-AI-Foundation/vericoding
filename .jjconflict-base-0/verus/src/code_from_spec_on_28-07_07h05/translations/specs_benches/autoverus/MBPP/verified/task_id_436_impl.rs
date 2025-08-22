use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

/* code modified by LLM (iteration 4): added helper lemma to prove filtering properties */
proof fn lemma_filter_subrange_extend(arr: Seq<i32>, i: int)
    requires 0 <= i < arr.len()
    ensures 
        arr.subrange(0, i + 1).filter(|x: i32| x < 0) == 
        if arr[i] < 0 {
            arr.subrange(0, i).filter(|x: i32| x < 0).push(arr[i])
        } else {
            arr.subrange(0, i).filter(|x: i32| x < 0)
        }
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(arr[i]));
    
    // The filtering of a sequence with one more element follows the pattern
    if arr[i] < 0 {
        assert(sub_i_plus_1.filter(|x: i32| x < 0) == sub_i.filter(|x: i32| x < 0).push(arr[i]));
    } else {
        assert(sub_i_plus_1.filter(|x: i32| x < 0) == sub_i.filter(|x: i32| x < 0));
    }
}

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): simplified loop using helper lemma */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 4): use lemma to establish filtering property */
        proof {
            lemma_filter_subrange_extend(arr@, i as int);
        }
        
        if arr[i] < 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): final assertion to establish postcondition */
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!