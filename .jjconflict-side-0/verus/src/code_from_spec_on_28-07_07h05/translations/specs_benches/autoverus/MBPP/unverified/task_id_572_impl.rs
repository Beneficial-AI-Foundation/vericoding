use vstd::prelude::*;

fn main() {}

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

/* code modified by LLM (iteration 1): added lemma to help prove subrange extension property */
proof fn lemma_subrange_extend(seq: Seq<i32>, i: int, key: i32)
    requires 0 <= i < seq.len()
    ensures count_frequency_rcr(seq.subrange(0, i + 1), key) == 
            count_frequency_rcr(seq.subrange(0, i), key) + 
            /* code modified by LLM (iteration 3): added explicit type annotation for integer literals */
            if seq[i] == key { 1int } else { 0int }
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(seq[i]));
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
        /* code modified by LLM (iteration 2): moved lemma call into proof block to fix type error */
        proof {
            lemma_subrange_extend(arr@, i as int, key);
        }
        
        if arr[i] == key {
            /* code modified by LLM (iteration 1): check for overflow before incrementing */
            assert(count < arr.len());
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    count
}

/* code modified by LLM (iteration 1): added lemma to help prove filter extension property */
proof fn lemma_filter_extend(seq: Seq<i32>, i: int)
    requires 0 <= i < seq.len()
    ensures seq.subrange(0, i + 1).filter(|x: i32| count_frequency_rcr(seq, x) == 1) ==
            seq.subrange(0, i).filter(|x: i32| count_frequency_rcr(seq, x) == 1) +
            if count_frequency_rcr(seq, seq[i]) == 1 { 
                seq![seq[i]] 
            } else { 
                seq![] 
            }
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    let elem = seq[i];
    
    assert(sub_i_plus_1 == sub_i.push(elem));
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
        /* code modified by LLM (iteration 2): moved lemma call into proof block to fix type error */
        proof {
            lemma_filter_extend(arr@, i as int);
        }
        
        let freq = count_frequency(arr, arr[i]);
        
        /* code modified by LLM (iteration 3): fixed type mismatch by casting arr[i] to int */
        assert(freq == count_frequency_rcr(arr@, arr[i as int]));
        
        if freq == 1 {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    result
}

} // verus!