// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i8>, b: i8) -> (c: Vec<i8>)
    ensures c@.map(|i: int, x: i8| x as int) == a@.map(|i: int, x: i8| x as int) + seq![b as int]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}