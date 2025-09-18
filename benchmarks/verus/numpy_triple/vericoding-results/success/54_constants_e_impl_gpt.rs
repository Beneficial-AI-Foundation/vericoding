// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn e_const() -> f64 { 2.718281828_f64 }
// </vc-helpers>

// <vc-spec>
fn e() -> (result: f64)
// </vc-spec>
// <vc-code>
{
    e_const()
}
// </vc-code>

}
fn main() {}