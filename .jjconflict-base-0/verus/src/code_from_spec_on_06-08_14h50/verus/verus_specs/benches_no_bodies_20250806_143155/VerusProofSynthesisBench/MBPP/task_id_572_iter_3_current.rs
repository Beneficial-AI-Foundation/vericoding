use vstd::prelude::*;

verus! {

spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> (result: int)
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
// pure-end

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    // post-conditions-start
    ensures
        count_frequency_rcr(arr@, key) == frequency,
    // post-conditions-end
{
    let mut count = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count == count_frequency_rcr(arr@.take(i as int), key),
        /* code modified by LLM (iteration 1): added decreases clause */
        decreases arr.len() - i
    {
        if arr[i] == key {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        /* code modified by LLM (iteration 1): fixed type mismatch by casting nat to int */
        assert(arr@.take(arr@.len() as int) == arr@);
    }
    
    count
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    // post-conditions-start
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.take(i as int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
        /* code modified by LLM (iteration 1): added decreases clause */
        decreases arr.len() - i
    {
        let freq = count_frequency(arr, arr[i]);
        if freq == 1 {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    
    proof {
        /* code modified by LLM (iteration 1): fixed type mismatch by casting nat to int */
        assert(arr@.take(arr@.len() as int) == arr@);
    }
    
    result
}

} // verus!

fn main() {}