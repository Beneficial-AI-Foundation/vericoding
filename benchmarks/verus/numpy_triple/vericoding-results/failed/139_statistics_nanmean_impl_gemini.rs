// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): a lemma for a postcondition */
proof fn lemma_no_nan_count(a: Seq<f32>)
    requires
        !contains_nan(a),
    ensures
        valid_indices_count(a) == a.len(),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_no_nan_count(a.skip(1));
    }
}

/* helper modified by LLM (iteration 5): fixed type annotation error for integer literals */
proof fn lemma_valid_indices_count_push(s: Seq<f32>, e: f32)
    ensures
        valid_indices_count(s.push(e)) == valid_indices_count(s) + if is_nan_f32(e) { 0nat } else { 1nat },
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_valid_indices_count_push(s.skip(1), e);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_nan_f32(x: f32) -> bool;

spec fn valid_indices_count(a: Seq<f32>) -> nat
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        if is_nan_f32(a[0]) {
            valid_indices_count(a.skip(1))
        } else {
            1 + valid_indices_count(a.skip(1))
        }
    }
}

spec fn has_valid_element(a: Seq<f32>) -> bool 
{
    valid_indices_count(a) > 0
}

spec fn all_nan(a: Seq<f32>) -> bool 
{
    valid_indices_count(a) == 0
}

spec fn contains_nan(a: Seq<f32>) -> bool
    decreases a.len()
{
    if a.len() == 0 {
        false
    } else {
        is_nan_f32(a[0]) || contains_nan(a.skip(1))
    }
}

fn nanmean(a: Vec<f32>) -> (result: f32)
    ensures 

        (has_valid_element(a@) ==> !is_nan_f32(result)) &&

        (all_nan(a@) ==> is_nan_f32(result)) &&

        (!is_nan_f32(result) ==> has_valid_element(a@)) &&

        (!contains_nan(a@) && a.len() > 0 ==> !is_nan_f32(result))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors (sub to subrange and integer types) */
    let mut sum: f32 = 0.0;
    let mut count: u64 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count as nat == valid_indices_count(a@.subrange(0, i as int)),
            if count > 0 { !is_nan_f32(sum) } else { sum == 0.0f32 },
        decreases a.len() - i
    {
        let x = a[i];
        proof {
            let s = a@.subrange(0, i as int);
            lemma_valid_indices_count_push(s, x);
        }

        if !x.is_nan() {
            sum = sum + x;
            count = count + 1;
        } 
        i = i + 1;
    }

    if count == 0 {
        f32::NAN
    } else {
        let count_f = count as f32;
        sum / count_f
    }
}
// </vc-code>

}
fn main() {}