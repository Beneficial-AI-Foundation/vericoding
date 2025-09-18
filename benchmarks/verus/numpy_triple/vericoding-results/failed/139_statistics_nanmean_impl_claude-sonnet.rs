// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): mark is_nan_f32 as uninterp and fix f32 comparison */
spec fn is_nan_f32(x: f32) -> bool {
    builtin_spec_is_nan_f32(x)
}

#[verifier::external_body]
spec fn builtin_spec_is_nan_f32(x: f32) -> bool uninterp;

proof fn lemma_valid_indices_count_properties(a: Seq<f32>)
    ensures
        valid_indices_count(a) <= a.len(),
        (valid_indices_count(a) == 0) == all_nan(a),
        (valid_indices_count(a) > 0) == has_valid_element(a)
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        lemma_valid_indices_count_properties(a.skip(1));
    }
}

proof fn lemma_contains_nan_properties(a: Seq<f32>)
    ensures
        contains_nan(a) == exists|i: int| 0 <= i < a.len() && is_nan_f32(a[i])
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        lemma_contains_nan_properties(a.skip(1));
    }
}

fn usize_to_f32(x: usize) -> (result: f32)
    requires x <= 16777216
    ensures result as usize == x
{
    x as f32
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
    /* code modified by LLM (iteration 5): fix is_nan_f32 call syntax and use proper external function */
    let mut sum: f32 = 0.0;
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            count <= i,
            count == valid_indices_count(a@.take(i as int))
    {
        if !a[i].is_nan() {
            sum = sum + a[i];
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        lemma_valid_indices_count_properties(a@);
        assert(valid_indices_count(a@.take(a.len() as int)) == valid_indices_count(a@));
    }
    
    if count == 0 {
        f32::NAN
    } else {
        sum / usize_to_f32(count)
    }
}
// </vc-code>

}
fn main() {}