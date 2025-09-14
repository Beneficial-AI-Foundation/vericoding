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
/* helper modified by LLM (iteration 5): helper lemma for sum_to properties */
proof fn sum_to_extend_lemma(s: Seq<i64>, i: int)
    requires 0 <= i < s.len()
    ensures sum_to(s.subrange(0, i + 1)) == sum_to(s.subrange(0, i)) + s[i]
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    assert(sub_i_plus_1.drop_last() == sub_i);
    assert(sub_i_plus_1.last() == s[i]);
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
    /* code modified by LLM (iteration 5): removed abs() call causing compilation error */
    let mut sum: i128 = 0;
    let mut i = start;
    while i <= end
        invariant
            start <= i <= end + 1,
            i <= arr.len(),
            sum == sum_to(arr@.subrange(start as int, i as int)),
        decreases end + 1 - i
    {
        proof {
            sum_to_extend_lemma(arr@.subrange(start as int, end + 1 as int), i - start);
        }
        assert(i < arr.len());
        let old_sum = sum;
        let ghost idx: int = i as int;
        sum = sum + arr[i] as i128;
        assert(sum == old_sum + arr@[idx] as i128);
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}