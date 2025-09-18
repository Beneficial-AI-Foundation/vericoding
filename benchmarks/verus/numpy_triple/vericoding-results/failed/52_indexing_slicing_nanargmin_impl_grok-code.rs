// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed duplicate spec fn declarations and argmin_non_nan_rec exec function */
proof fn f32_le_trans(a: f32, b: f32, c: f32)
    requires f32_le(a, b), f32_le(b, c)
    ensures f32_le(a, c)
{ }
/* helper modified by LLM (iteration 5): added lemma to connect spec f32_is_nan to exec is_nan */
proof fn f32_is_nan_eq_is_nan(x: f32) ensures f32_is_nan(x) <==> x.is_nan() { }
// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed invalid assert forall for is_nan, added proof assertions to connect exec and spec after finding min */
{
    proof {
        assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && !f32_is_nan(a[i]) && !f32_is_nan(a[j]) ==> 
            (a@[i as usize] <= a@[j as usize]) == f32_le(a[i], a[j]) && 
            (a@[i as usize] == a@[j as usize]) == (f32_le(a[i], a[j]) && f32_le(a[j], a[i]));
    }
    let mut min_i: usize = 0;
    let mut min_val: f32 = f32::INFINITY;
    let mut found = false;
    for i in 0..a.len() {
        if !a[i].is_nan() {
            if !found {
                min_i = i;
                min_val = a[i];
                found = true;
            } else {
                if a[i] < min_val {
                    min_i = i;
                    min_val = a[i];
                } else if a[i] == min_val && i < min_i {
                    min_i = i;
                    min_val = a[i];
                }
            }
        }
    }
    proof {
        assert (!a[min_i].is_nan());
        f32_is_nan_eq_is_nan(a@[min_i as int]);
        assert (!f32_is_nan(a@[min_i as int]));
    }
    min_i
}
// </vc-code>

}
fn main() {}