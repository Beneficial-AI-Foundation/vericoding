// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma for sum_to base case and extension */
proof fn sum_to_empty(arr: Seq<i64>, start: int)
    requires
        0 <= start <= arr.len(),
    ensures
        sum_to(arr.subrange(start, start)) == 0,
{
    assert(arr.subrange(start, start).len() == 0);
}

proof fn sum_to_extend(arr: Seq<i64>, start: int, end: int, i: int)
    requires
        0 <= start <= i < end,
        end <= arr.len(),
    ensures
        sum_to(arr.subrange(start, i + 1)) == sum_to(arr.subrange(start, i)) + arr[i],
{
    let sub = arr.subrange(start, i + 1);
    let sub_prev = arr.subrange(start, i);
    assert(sub.drop_last() =~= sub_prev);
    assert(sub.last() == arr[i]);
}
// </vc-helpers>

// <vc-spec>
fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)

    requires
        0 <= start <= end,
        start <= end < arr.len(),

    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariant and overflow check */
    let mut sum: i128 = 0;
    let mut i: usize = start;
    
    proof {
        sum_to_empty(arr@, start as int);
    }
    
    while i <= end
        invariant
            start <= i <= end + 1,
            end < arr.len(),
            sum == sum_to(arr@.subrange(start as int, i as int)),
            forall|j: int| start <= j < i ==> -9223372036854775808 <= arr@[j] <= 9223372036854775807,
        decreases end - i,
    {
        proof {
            assert(i < arr.len());
            sum_to_extend(arr@, start as int, (end + 1) as int, i as int);
        }
        sum = sum + arr[i] as i128;
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}