// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn one_usize() -> usize { 1usize }

proof fn lemma_one_value()
    ensures one_usize() == 1usize
{ }
// </vc-helpers>

// <vc-spec>
fn ndim<T>(a: &Vec<T>) -> (result: usize)
    ensures result == 1
// </vc-spec>
// <vc-code>
{
    1usize
}
// </vc-code>

}
fn main() {}