use vstd::prelude::*;

fn main() {}

verus! {

spec fn sum_negative_to(seq: Seq<i64>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut sum: i128 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            sum == sum_negative_to(arr@.subrange(0, i as int)),
    {
        if arr[i] < 0 {
            sum = sum + arr[i] as i128;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    }
    
    sum
}

} // verus!