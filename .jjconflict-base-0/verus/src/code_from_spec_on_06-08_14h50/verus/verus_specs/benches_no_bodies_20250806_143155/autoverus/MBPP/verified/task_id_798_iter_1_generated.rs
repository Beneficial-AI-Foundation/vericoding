For the `sum()` function, I need to implement an iterative approach that computes the same result. I'll use a loop with an invariant that relates the partial sum to the spec function.

use vstd::prelude::*;

fn main() {
}

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

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut sum: i128 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            sum == sum_to(arr@.subrange(0, i as int)),
    {
        sum = sum + arr[i] as i128;
        i = i + 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    sum
}

} // verus!