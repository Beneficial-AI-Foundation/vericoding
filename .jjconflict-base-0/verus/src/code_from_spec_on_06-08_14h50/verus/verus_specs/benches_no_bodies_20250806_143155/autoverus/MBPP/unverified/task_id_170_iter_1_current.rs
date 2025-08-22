use vstd::prelude::*;

fn main() {}

verus! {

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut sum: i128 = 0;
    let mut i = start;
    
    while i <= end
        invariant
            start <= i <= end + 1,
            sum == sum_to(arr@.subrange(start as int, i as int)),
    {
        sum = sum + arr[i] as i128;
        i = i + 1;
    }
    
    sum
}

} // verus!