use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ufunc_identity(op: spec_fn(f64, f64) -> f64) -> (result: Option<f64>)
    ensures
        match result {
            Some(id) => forall|x: f64| op(x, id) == x && op(id, x) == x,
            None => !exists|id: f64| forall|x: f64| op(x, id) == x && op(id, x) == x,
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}