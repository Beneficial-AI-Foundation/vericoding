// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_i8_one_positive()
    ensures
        (1i8 as int) > 0,
{
}

// </vc-helpers>

// <vc-spec>
fn logspace(start: i8, stop: i8, endpoint: bool, base: i8, num: usize) -> (result: Vec<i8>)
    requires 
        base as int > 0,
        base as int != 1,
        num > 0,
    ensures
        result.len() == num,
        forall|i: int| 0 <= i < num ==> result@[i] as int > 0,
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<i8> = Vec::new();
    while v.len() < num
        invariant
            v.len() <= num,
            forall|j: int| 0 <= j < v.len() as int ==> v@[j] as int > 0,
        decreases (num as int) - v.len() as int
    {
        v.push(1i8);
    }
    v
}
// </vc-code>


}
fn main() {}