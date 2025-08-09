use vstd::prelude::*;

fn main() {
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

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut count = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == count_frequency_rcr(arr@.take(i as int), key),
    {
        if arr[i] == key {
            count += 1;
        }
        i += 1;
    }
    
    proof {
        /* code modified by LLM (iteration 1): cast nat to int for take method */
        assert(arr@.take(arr@.len() as int) =~= arr@);
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
            result@ == arr@.take(i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        if count_frequency(arr, arr[i]) == 1 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        /* code modified by LLM (iteration 1): cast nat to int for take method */
        assert(arr@.take(arr@.len() as int) =~= arr@);
    }
    
    result
}

} // verus!