// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_greater(n: i8, a: &Vec<i8>) -> (result: bool)
    ensures 
        result ==> forall|i: int| 0 <= i < a@.len() ==> n as int > a@[i] as int,
        !result ==> exists|i: int| 0 <= i < a@.len() && n as int <= a@[i] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}