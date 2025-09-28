// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn shape_lemma<T>(a: &Vec<T>) -> (result: usize)
    ensures
        result == a.len(),
{
    a.len()
}
// </vc-helpers>

// <vc-spec>
fn shape<T>(a: &Vec<T>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
{
    let result = a.len();
    result
}
// </vc-code>

}
fn main() {}