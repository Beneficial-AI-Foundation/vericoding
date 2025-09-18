// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty helper section, no changes needed */
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
/* code modified by LLM (iteration 5): Fixed compilation error by removing extraneous braces around the invariant. The previous change had re-introduced a syntax issue that was already properly handled by the syntax of the invariant keyword. */
{
    let mut sum: f32 = 0.0;
    let mut count: u64 = 0;

    let a_seq = a@;

    let mut i: u64 = 0;
    while i < a.len() as u64
        invariant a.len() == a_seq.len(),
        invariant all_nan(a_seq.subsequence(0, i as nat)) == (count == 0 && sum == 0.0),
        invariant !all_nan(a_seq.subsequence(0, i as nat)) ==> (count > 0),
        invariant forall |j: int| 0 <= j < i as int && !is_nan_f32(a_seq[j]) ==> count > 0,
        invariant forall |j: int| 0 <= j < i as int && is_nan_f32(a_seq[j]) ==> true,
        invariant sum == {
            let mut current_sum_local: f32 = 0.0;
            let mut k: nat = 0;
            while k < i
                invariant k <= i,
                invariant forall |l: nat| 0 <= l < k && !is_nan_f32(a_seq[l]) ==> current_sum_local == current_sum_local + a_seq[l]
            {
                if !is_nan_f32(a_seq[k]) {
                    current_sum_local = current_sum_local + a_seq[k];
                }
                k = k + 1;
            }
            current_sum_local
        },
        invariant count == {
            let mut current_count_local: u64 = 0;
            let mut k: nat = 0;
            while k < i
                invariant k <= i,
                invariant forall |l: nat| 0 <= l < k && !is_nan_f32(a_seq[l]) ==> current_count_local == current_count_local + 1
            {
                if !is_nan_f32(a_seq[k]) {
                    current_count_local = current_count_local + 1;
                }
                k = k + 1;
            }
            current_count_local
        },
        decreases a.len() - i
    {
        let val = a[i as usize];
        if !is_nan_f32(val) {
            sum = sum + val;
            count = count + 1;
        }
        i = i + 1;
    }

    if count > 0 {
        sum / count as f32
    } else {
        f32::NAN
    }
}
// </vc-code>

}
fn main() {}