use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

/* code modified by LLM (iteration 1): added lemma to help prove subrange properties */
proof fn lemma_subrange_extend(seq: Seq<i32>, i: int, key: i32)
    requires 0 <= i < seq.len()
    ensures count_frequency_rcr(seq.subrange(0, i + 1), key) == 
            count_frequency_rcr(seq.subrange(0, i), key) + if seq[i] == key { 1int } else { 0int }
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    
    assert(sub_i_plus_1.last() == seq[i]);
    assert(sub_i_plus_1.drop_last() == sub_i);
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut count = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == count_frequency_rcr(arr@.subrange(0, i as int), key),
            /* code modified by LLM (iteration 1): added bound invariant to prevent overflow */
            count <= i,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 1): added proof to maintain invariant */
        proof {
            lemma_subrange_extend(arr@, i as int, key);
        }
        
        /* code modified by LLM (iteration 1): removed 'as int' cast from executable code */
        if arr[i] == key {
            /* code modified by LLM (iteration 1): added assertion to prove no overflow */
            assert(count < arr.len());
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    count
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 1): removed 'as int' cast from executable code */
        let freq = count_frequency(arr, arr[i]);
        
        /* code modified by LLM (iteration 1): added proof to maintain invariant */
        proof {
            let current_elem = arr[i as int];
            let sub_i = arr@.subrange(0, i as int);
            let sub_i_plus_1 = arr@.subrange(0, (i + 1) as int);
            
            assert(sub_i_plus_1 == sub_i.push(current_elem));
            
            // The filter property is maintained when we extend the subrange
            if freq == 1 {
                assert(count_frequency_rcr(arr@, current_elem) == 1);
            } else {
                assert(count_frequency_rcr(arr@, current_elem) != 1);
            }
        }
        
        if freq == 1 {
            /* code modified by LLM (iteration 1): removed 'as int' cast from executable code */
            result.push(arr[i]);
        }
        i = i + 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    result
}

} // verus!