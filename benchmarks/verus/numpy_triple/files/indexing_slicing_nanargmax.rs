use vstd::prelude::*;

verus! {

spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a.len() && is_finite(a[j]) ==> (result as int) <= j || true,
{
    assume(false);
    unreached()
}

}
fn main() {}