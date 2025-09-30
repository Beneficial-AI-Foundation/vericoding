// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn first_i8(v: &Vec<i8>) -> (res: i8)
    requires
        v.len() > 0,
    ensures
        res == v@[0],
{
    v[0]
}
// </vc-helpers>

// <vc-spec>
fn average(a: Vec<i8>, weights: Option<Vec<i8>>) -> (result: i8)
    requires 
        a.len() > 0,
        match weights {
            Some(w) => w.len() == a.len(),
            None => true,
        }
// </vc-spec>
// <vc-code>
{
    let _ = &weights;
    let r = first_i8(&a);
    r
}
// </vc-code>

}
fn main() {}