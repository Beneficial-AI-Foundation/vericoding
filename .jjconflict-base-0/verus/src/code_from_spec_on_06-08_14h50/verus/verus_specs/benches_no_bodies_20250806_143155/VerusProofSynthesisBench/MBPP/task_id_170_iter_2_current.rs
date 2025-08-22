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

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    // pre-conditions-start
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
    // post-conditions-end
{
    let mut sum: i128 = 0;
    let mut i = start;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i <= end
        invariant
            start <= i <= end + 1,
            sum == sum_to(arr@.subrange(start as int, i as int)),
        decreases end - i
    {
        sum = sum + arr[i] as i128;
        
        // Proof that the invariant is maintained
        proof {
            let subseq_next = arr@.subrange(start as int, (i + 1) as int);
            let subseq_curr = arr@.subrange(start as int, i as int);
            assert(subseq_next == subseq_curr.push(arr@[i as int]));
            assert(sum_to(subseq_next) == sum_to(subseq_curr) + arr@[i as int]);
        }
        
        i = i + 1;
    }
    
    sum
}

} // verus!

fn main() {}