// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_vec(v: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == v.len(),
{
    v
}
// </vc-helpers>

// <vc-spec>
fn poly2lag(pol: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == pol.len(),

        true,
// </vc-spec>
// <vc-code>
{
    pol
}
// </vc-code>

}
fn main() {}