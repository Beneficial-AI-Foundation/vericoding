// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added curly braces around uninterp function */
spec fn is_nan_f32(x: f32) -> bool {
    uninterp
}

proof fn lemma_valid_count_properties(a: Seq<f32>)
    ensures
        all_nan(a) <==> valid_indices_count(a) == 0,
        has_valid_element(a) <==> valid_indices_count(a) > 0,
        !has_valid_element(a) <==> all_nan(a)
{
}

proof fn lemma_no_nan_implies_valid(a: Seq<f32>)
    requires !contains_nan(a), a.len() > 0
    ensures has_valid_element(a)
    decreases a.len()
{
    if a.len() == 1 {
        assert(!is_nan_f32(a[0]));
        assert(valid_indices_count(a) == 1);
    } else {
        lemma_no_nan_implies_valid(a.skip(1));
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
    /* code modified by LLM (iteration 5): fixed cast from usize to f32 to avoid unsupported cast */
    let mut sum: f32 = 0.0;
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            count <= i
    {
        if !a[i].is_nan() {
            sum = sum + a[i];
            count = count + 1;
        }
        i = i + 1;
    }
    
    if count == 0 {
        f32::NAN
    } else {
        let count_f32 = count as f32;
        sum / count_f32
    }
}
// </vc-code>

}
fn main() {}