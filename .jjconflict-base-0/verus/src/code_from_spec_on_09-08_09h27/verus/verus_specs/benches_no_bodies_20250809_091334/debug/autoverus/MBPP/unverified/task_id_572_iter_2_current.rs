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
    {
        if arr[i] == key {
            count += 1;
        }
        i += 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) == arr@);
        lemma_count_frequency_equivalence(arr@, key);
    }
    
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
    {
        let freq = count_frequency(arr, arr[i]);
        if freq == 1 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) == arr@);
    }
    
    result
}

proof fn lemma_count_frequency_equivalence(seq: Seq<i32>, key: i32)
    ensures count_frequency_rcr(seq, key) == count_frequency_rcr(seq.subrange(0, seq.len() as int), key)
{
    if seq.len() == 0 {
    } else {
        lemma_count_frequency_subrange_recursive(seq, key, seq.len() as int);
    }
}

proof fn lemma_count_frequency_subrange_recursive(seq: Seq<i32>, key: i32, end: int)
    requires 0 <= end <= seq.len()
    ensures count_frequency_rcr(seq.subrange(0, end), key) == 
            if end == 0 { 0 } else { 
                count_frequency_rcr(seq.subrange(0, end - 1), key) + 
                if seq[end - 1] == key { 1int } else { 0int }
            }
    decreases end
{
    if end == 0 {
    } else if end == 1 {
        /* code modified by LLM (iteration 1): added explicit type annotations to fix compilation error */
        assert(seq.subrange(0, 1).drop_last() == seq.subrange(0, 0));
    } else {
        lemma_count_frequency_subrange_recursive(seq, key, end - 1);
        assert(seq.subrange(0, end).drop_last() == seq.subrange(0, end - 1));
        assert(seq.subrange(0, end).last() == seq[end - 1]);
    }
}

} // verus!