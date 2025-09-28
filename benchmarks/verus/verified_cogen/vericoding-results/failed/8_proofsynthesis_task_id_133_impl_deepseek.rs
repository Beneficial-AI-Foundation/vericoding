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
/* helper modified by LLM (iteration 5): Fixed syntax error in lemma signature and implementation */

spec fn is_negative(x: i64) -> bool {
    x < 0
}

proof fn sum_negative_to_recursive(s: Seq<i64>, i: int) -> (res: int)
    requires
        0 <= i <= s.len(),
    decreases s.len() - i,
    ensures
        res == sum_negative_to(s.subrange(i, s.len())),
{
    if i == s.len() {
        0
    } else {
        let remainder = sum_negative_to_recursive(s, i + 1);
        if is_negative(s[i]) {
            s[i] as int + remainder
        } else {
            remainder
        }
    }
}

proof fn lemma_sum_negative_to_whole_seq(s: Seq<i64>)
    ensures
        sum_negative_to_recursive(s, 0) == sum_negative_to(s),
{
    if s.len() == 0 {
        assert(sum_negative_to_recursive(s, 0) == 0);
        assert(sum_negative_to(s) == 0);
    } else {
        let prev = s.drop_last();
        lemma_sum_negative_to_whole_seq(prev);
        
        let last_contrib = if is_negative(s.last()) { s.last() as int } else { 0 };
        assert(sum_negative_to(s) == sum_negative_to(prev) + last_contrib);
        
        let recursive_sum = sum_negative_to_recursive(s, 0);
        assert(recursive_sum == if is_negative(s[0]) { s[0] as int + sum_negative_to_recursive(s, 1) } else { sum_negative_to_recursive(s, 1) });
        assert(sum_negative_to_recursive(s, 1) == sum_negative_to(s.subrange(1, s.len())));
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
    /* code modified by LLM (iteration 5): Fixed compilation error and improved loop implementation */
    let mut sum: i128 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            sum == sum_negative_to(arr@.subrange(0, i)),
            i <= arr.len(),
    {
        if arr[i] < 0 {
            sum = sum + arr[i] as i128;
        }
        i = i + 1;
    }
    
    proof {
        lemma_sum_negative_to_whole_seq(arr@);
        assert(sum_negative_to_recursive(arr@, 0) == sum_negative_to(arr@));
        assert(sum == sum_negative_to(arr@.subrange(0, arr.len())));
        assert(arr@.subrange(0, arr.len()) == arr@);
    }
    
    sum
}
// </vc-code>

}
fn main() {}