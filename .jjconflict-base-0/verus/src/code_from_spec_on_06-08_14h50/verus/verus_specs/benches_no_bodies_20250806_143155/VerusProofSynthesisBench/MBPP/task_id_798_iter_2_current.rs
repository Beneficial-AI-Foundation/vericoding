use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// pure-end

fn sum(arr: &Vec<i64>) -> (sum: i128)
    // post-conditions-start
    ensures
        sum_to(arr@) == sum,
    // post-conditions-end
{
    let mut sum = 0i128;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for the while loop */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == sum_to(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        sum = sum + arr[i] as i128;
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): added proof block to establish final postcondition */
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    sum
}

} // verus!

fn main() {}