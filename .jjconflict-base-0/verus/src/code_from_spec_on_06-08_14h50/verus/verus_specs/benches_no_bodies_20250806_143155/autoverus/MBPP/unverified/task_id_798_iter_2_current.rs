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

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut result: i128 = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause and proof block for postcondition */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result == sum_to(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        result = result + arr[i] as i128;
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): added proof to establish postcondition */
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    result
}

} // verus!