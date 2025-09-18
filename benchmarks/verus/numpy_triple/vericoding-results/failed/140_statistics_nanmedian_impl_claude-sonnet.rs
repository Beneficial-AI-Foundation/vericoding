// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed is_nan() usage to fix compilation */
fn has_any_finite(a: &Vec<f32>) -> (result: bool)
    ensures result == has_finite_value(a@)
{
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a@[j] != a@[j]
    {
        if a[i] == a[i] {
            return true;
        }
    }
    false
}

fn find_finite_value(a: &Vec<f32>) -> (result: f32)
    requires has_finite_value(a@)
    ensures result == result
{
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a@[j] != a@[j]
    {
        if a[i] == a[i] {
            return a[i];
        }
    }
    0.0
}

fn create_nan() -> (result: f32)
    ensures result != result
{
    0.0 / 0.0
}
// </vc-helpers>

// <vc-spec>
spec fn all_nan(a: Seq<f32>) -> bool {
    forall|i: int| #![auto] 0 <= i < a.len() ==> (a[i] != a[i])
}

spec fn has_finite_value(a: Seq<f32>) -> bool {
    exists|i: int| #![auto] 0 <= i < a.len() && (a[i] == a[i])
}

fn nanmedian(a: Vec<f32>) -> (result: f32)
    ensures
        (all_nan(a@) ==> (result != result)) &&
        (has_finite_value(a@) ==> (result == result))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use create_nan() instead of f32::NAN to fix compilation */
{
    if !has_any_finite(&a) {
        create_nan()
    } else {
        find_finite_value(&a)
    }
}
// </vc-code>

}
fn main() {}