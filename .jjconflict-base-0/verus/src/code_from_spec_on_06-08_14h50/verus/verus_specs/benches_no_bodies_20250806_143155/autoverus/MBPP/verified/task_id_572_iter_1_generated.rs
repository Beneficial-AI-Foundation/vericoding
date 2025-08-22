use vstd::prelude::*;

fn main() {
    // Simple main function - no specific requirements given
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
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            count_frequency_rcr(arr@.subrange(0, i as int), key) == count,
    {
        if arr[i] == key {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr@.len()) =~= arr@);
    }
    
    count
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    {
        let freq = count_frequency(arr, arr[i]);
        if freq == 1 {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr@.len()) =~= arr@);
    }
    
    result
}

} // verus!