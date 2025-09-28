// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_negative_to(seq: Seq<i64>) -> (res: int)
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to handle sum bounds for negative values */
proof fn lemma_sum_negative_extend(s: Seq<i64>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        sum_negative_to(s.take(i + 1)) == sum_negative_to(s.take(i)) + if s[i] < 0 { s[i] as int } else { 0 },
{
    let s_take_i = s.take(i);
    let s_take_i_plus_1 = s.take(i + 1);
    assert(s_take_i_plus_1 == s_take_i.push(s[i]));
    assert(s_take_i_plus_1.drop_last() == s_take_i);
    assert(s_take_i_plus_1.last() == s[i]);
}

proof fn lemma_sum_negative_bounds(s: Seq<i64>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        sum_negative_to(s.take(i)) <= 0,
        sum_negative_to(s.take(i)) >= -(i as int) * (i64::MAX as int + 1),
    decreases i,
{
    if i == 0 {
        assert(s.take(0).len() == 0);
        assert(sum_negative_to(s.take(0)) == 0);
    } else {
        lemma_sum_negative_bounds(s, i - 1);
        lemma_sum_negative_extend(s, i - 1);
        let prev_sum = sum_negative_to(s.take(i - 1));
        let curr_sum = sum_negative_to(s.take(i));
        if s[i - 1] < 0 {
            assert(curr_sum == prev_sum + s[i - 1] as int);
            assert(s[i - 1] as int >= -(i64::MAX as int + 1));
            assert(curr_sum <= prev_sum);
            assert(curr_sum <= 0);
        } else {
            assert(curr_sum == prev_sum);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)

    ensures
        sum_negative_to(arr@) == sum_neg,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed array indexing with as int conversion */
    let mut sum: i128 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == sum_negative_to(arr@.take(i as int)),
            sum <= 0,
            sum >= -(i as i128) * (i64::MAX as i128 + 1),
        decreases arr.len() - i,
    {
        let old_i = i;
        let old_sum = sum;
        
        if arr[i as int] < 0 {
            assert(arr[i as int] >= i64::MIN);
            assert(arr[i as int] as i128 >= i64::MIN as i128);
            assert(old_sum + arr[i as int] as i128 >= old_sum + i64::MIN as i128);
            sum = sum + arr[i as int] as i128;
        }
        
        i = i + 1;
        
        proof {
            lemma_sum_negative_extend(arr@, old_i as int);
            lemma_sum_negative_bounds(arr@, i as int);
            assert(arr@.take(i as int) == arr@.take(old_i as int + 1));
            if arr[old_i as int] < 0 {
                assert(sum == old_sum + arr[old_i as int] as i128);
                assert(sum_negative_to(arr@.take(i as int)) == sum_negative_to(arr@.take(old_i as int)) + arr[old_i as int] as int);
                assert(sum as int == sum_negative_to(arr@.take(i as int)));
            } else {
                assert(sum == old_sum);
                assert(sum_negative_to(arr@.take(i as int)) == sum_negative_to(arr@.take(old_i as int)));
            }
        }
    }
    
    assert(arr@ =~= arr@.take(arr.len() as int));
    sum
}
// </vc-code>

}
fn main() {}