// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define is_nan_f32 using IEEE NaN equality */
spec fn is_nan_f32(x: f32) -> bool { x != x }

/* helper modified by LLM (iteration 5): valid_indices_count_by_value computes non-NaN count using equality test */
spec fn valid_indices_count_by_value(a: Seq<f32>) -> nat
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        if a[0] == a[0] {
            1 + valid_indices_count_by_value(a.skip(1))
        } else {
            valid_indices_count_by_value(a.skip(1))
        }
    }
}

/* helper modified by LLM (iteration 5): relate valid_indices_count (uses is_nan_f32) to value-based count */
fn valid_indices_count_matches(a: Seq<f32>)
    ensures
        valid_indices_count(a) == valid_indices_count_by_value(a),
    decreases a.len()
{
    proof {
        if a.len() == 0 {
            assert(valid_indices_count(a) == 0);
            assert(valid_indices_count_by_value(a) == 0);
        } else {
            assert(valid_indices_count(a) ==
                if is_nan_f32(a[0]) { valid_indices_count(a.skip(1)) } else { 1 + valid_indices_count(a.skip(1)) });
            assert(valid_indices_count_by_value(a) ==
                if a[0] == a[0] { 1 + valid_indices_count_by_value(a.skip(1)) } else { valid_indices_count_by_value(a.skip(1)) });
            if a[0] == a[0] {
                valid_indices_count_matches(a.skip(1));
                assert(valid_indices_count(a.skip(1)) == valid_indices_count_by_value(a.skip(1)));
                assert(valid_indices_count(a) == 1 + valid_indices_count(a.skip(1)));
                assert(valid_indices_count_by_value(a) == 1 + valid_indices_count_by_value(a.skip(1)));
                assert(valid_indices_count(a) == valid_indices_count_by_value(a));
            } else {
                valid_indices_count_matches(a.skip(1));
                assert(valid_indices_count(a.skip(1)) == valid_indices_count_by_value(a.skip(1)));
                assert(valid_indices_count(a) == valid_indices_count(a.skip(1)));
                assert(valid_indices_count_by_value(a) == valid_indices_count_by_value(a.skip(1)));
                assert(valid_indices_count(a) == valid_indices_count_by_value(a));
            }
        }
    }
}

/* helper modified by LLM (iteration 5): trivial add preservation lemma for non-NaN */
fn add_preserves_non_nan(a: f32, b: f32)
    requires
        a == a, b == b,
    ensures
        (a + b) == (a + b),
{
    proof {
        assert((a + b) == (a + b));
    }
}

/* helper modified by LLM (iteration 5): trivial div preservation lemma for non-NaN */
fn div_preserves_non_nan(numer: f32, denom: f32)
    requires
        numer == numer, denom == denom, denom != 0.0,
    ensures
        (numer / denom) == (numer / denom),
{
    proof {
        assert((numer / denom) == (numer / denom));
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
    /* code modified by LLM (iteration 5): compute mean ignoring NaNs using equality test */
    let mut sum: f32 = 0.0;
    let mut cnt: nat = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            cnt == valid_indices_count_by_value(a@.slice(0, i)),
        decreases a.len() - i
    {
        let x: f32 = a.index(i);
        if x == x {
            add_preserves_non_nan(sum, x);
            sum = sum + x;
            cnt = cnt + 1;
        }
        i = i + 1;
    }

    if cnt == 0 {
        f32::NAN
    } else {
        div_preserves_non_nan(sum, cnt as f32);
        sum / (cnt as f32)
    }
}

// </vc-code>

}
fn main() {}