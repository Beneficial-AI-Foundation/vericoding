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
/* helper modified by LLM (iteration 5): added lemma to prove subrange property for sum_to */
proof fn sum_to_subrange_lemma(arr: Seq<i64>, i: int)
    requires
        0 <= i < arr.len(),
    ensures
        sum_to(arr.subrange(0, i + 1)) == sum_to(arr.subrange(0, i)) + arr[i],
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    assert(sub_i_plus_1.drop_last() =~= sub_i);
    assert(sub_i_plus_1.last() == arr[i]);
}
// </vc-helpers>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (result: i128)

    ensures
        sum_to(arr@) == result
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add overflow checks and fix assertion placement */
    let mut result: i128 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result == sum_to(arr@.subrange(0, i as int)),
            result >= i128::MIN,
            result <= i128::MAX,
        decreases arr.len() - i
    {
        let arr_val = arr[i] as i128;
        assert(result >= i128::MIN && result <= i128::MAX);
        assert(arr_val >= i64::MIN as i128 && arr_val <= i64::MAX as i128);
        assert(result + arr_val >= i128::MIN && result + arr_val <= i128::MAX);
        result = result + arr_val;
        i = i + 1;
        proof {
            sum_to_subrange_lemma(arr@, (i - 1) as int);
        }
    }
    proof {
        assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    }
    result
}
// </vc-code>

}
fn main() {}