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
/* helper modified by LLM (iteration 5): fixed precondition and proof logic issues */
proof fn count_val_drop_lemma(val: i32, xs: Seq<i32>)
    requires xs.len() > 0
    ensures count_val(val, xs) == (if xs[0] == val { 1nat } else { 0nat }) + count_val(val, xs.drop_first())
{
}

proof fn is_subsequence_trans_lemma(xs: Seq<i32>, ys: Seq<i32>, zs: Seq<i32>)
    requires is_subsequence(xs, ys), is_subsequence(ys, zs)
    ensures is_subsequence(xs, zs)
    decreases xs.len() + ys.len() + zs.len()
{
    if xs.len() == 0 {
        return;
    }
    if ys.len() == 0 {
        return;
    }
    if zs.len() == 0 {
        return;
    }
    
    if xs[0] == ys[0] {
        if ys[0] == zs[0] {
            is_subsequence_trans_lemma(xs.drop_first(), ys.drop_first(), zs.drop_first());
        } else {
            is_subsequence_trans_lemma(xs, ys, zs.drop_first());
        }
    } else {
        if ys[0] == zs[0] {
            is_subsequence_trans_lemma(xs, ys.drop_first(), zs.drop_first());
        } else {
            is_subsequence_trans_lemma(xs, ys.drop_first(), zs.drop_first());
        }
    }
}

proof fn filter_is_subsequence_lemma(xs: Seq<i32>, f: spec_fn(i32) -> bool)
    ensures is_subsequence(xs.filter(f), xs)
    decreases xs.len()
{
    if xs.len() == 0 {
        return;
    }
    filter_is_subsequence_lemma(xs.drop_first(), f);
}

proof fn count_val_filter_lemma(val: i32, xs: Seq<i32>, f: spec_fn(i32) -> bool)
    ensures count_val(val, xs.filter(f)) <= count_val(val, xs)
    decreases xs.len()
{
    if xs.len() == 0 {
        return;
    }
    count_val_filter_lemma(val, xs.drop_first(), f);
    if f(xs[0]) {
        // Element is kept, count is preserved
    } else {
        // Element is filtered out, count in filtered is <= count in original
    }
}

proof fn count_val_append_lemma(val: i32, xs: Seq<i32>, ys: Seq<i32>)
    ensures count_val(val, xs + ys) == count_val(val, xs) + count_val(val, ys)
    decreases xs.len()
{
    if xs.len() == 0 {
        return;
    }
    count_val_append_lemma(val, xs.drop_first(), ys);
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
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut result = Vec::new();
    
    // First pass: collect non-zero elements
    for i in 0..xs.len()
        invariant
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> result[k] != 0,
            is_subsequence(result@, xs@),
            result@ == xs@.subrange(0, i as int).filter(|x: i32| x != 0)
    {
        if xs[i] != 0 {
            result.push(xs[i]);
        }
    }
    
    let non_zero_count = result.len();
    
    // Second pass: append zeros
    while result.len() < xs.len()
        invariant
            non_zero_count <= result.len() <= xs.len(),
            forall|k: int| 0 <= k < non_zero_count ==> result[k] != 0,
            forall|k: int| non_zero_count <= k < result.len() ==> result[k] == 0,
            result@.subrange(0, non_zero_count as int) == xs@.filter(|x: i32| x != 0)
        decreases xs.len() - result.len()
    {
        result.push(0);
    }
    
    proof {
        filter_is_subsequence_lemma(xs@, |x: i32| x != 0);
        count_val_append_lemma(0, result@.subrange(0, non_zero_count as int), result@.subrange(non_zero_count as int, result.len() as int));
    }
    
    result
}
// </vc-code>

}
fn main() {}