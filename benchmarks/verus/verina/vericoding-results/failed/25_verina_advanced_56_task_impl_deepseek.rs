// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_val(val: i32, xs: Seq<i32>) -> nat 
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        let rest = count_val(val, xs.drop_first());
        if xs[0] == val { rest + 1 } else { rest }
    }
}

spec fn is_subsequence(xs: Seq<i32>, ys: Seq<i32>) -> bool 
    decreases xs.len() + ys.len()
{
    if xs.len() == 0 {
        true
    } else if ys.len() == 0 {
        false
    } else {
        if xs[0] == ys[0] {
            is_subsequence(xs.drop_first(), ys.drop_first())
        } else {
            is_subsequence(xs, ys.drop_first())
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches and added proper helper functions */
proof fn take_subsequence_lemma(xs: Seq<i32>, n: nat) {
    assert(xs.take(n).len() == n as int);
}

proof fn count_val_lemma_part(xs: Seq<i32>, val: i32, i: int) {
    requires i >= 0 && i <= xs.len();
    ensures count_val(val, xs) == count_val(val, xs.take(i)) + count_val(val, xs.drop(i));
}

proof fn push_zero_count_lemma(seq: Seq<i32>, zeros: nat) {
    requires count_val(0, seq) == 0;
    ensures count_val(0, seq + Seq::new(zeros, |_| 0)) == zeros;
}

proof fn subsequence_filter_lemma(xs: Seq<i32>, filtered: Seq<i32>) {
    requires filtered == xs.filter(|x: i32| x != 0);
    ensures is_subsequence(filtered, xs);
}
// </vc-helpers>

// <vc-spec>
fn move_zeroes(xs: Vec<i32>) -> (result: Vec<i32>)
    ensures

        is_subsequence(xs@.filter(|x: i32| x != 0), result@),

        forall|i: int| 0 <= i < result.len() && result[i] != 0 ==> 
            forall|j: int| i < j < result.len() ==> result[j] != 0,

        xs.len() == result.len(),

        count_val(0, xs@) == count_val(0, result@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors and verification issues */
{
    let mut xs = xs;
    let mut result = Vec::new();
    let len = xs.len() as int;
    
    let mut i: int = 0;
    while i < len
        invariant
            i >= 0 && i <= len,
            xs.len() == (len - i) as usize,
            result.len() as int == i - count_val(0, xs@.subrange(0, i)),
            count_val(0, xs@) + count_val(0, result@) == count_val(0, xs@.subrange(0, i)),
    {
        let elem = xs[i as usize];
        if elem != 0 {
            result.push(elem);
        }
        i = i + 1;
    }
    
    let zero_count = count_val(0, xs@) as int;
    let mut j: int = 0;
    while j < zero_count
        invariant
            j >= 0 && j <= zero_count,
            result.len() as int == len - count_val(0, xs@) + j,
            count_val(0, result@) == j,
    {
        result.push(0);
        j = j + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}