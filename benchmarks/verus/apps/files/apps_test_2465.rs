// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(angles: Seq<int>) -> bool {
    forall|i: int| 0 <= i < angles.len() ==> 1 <= angles[i] < 180
}

spec fn gcd(a: int, b: int) -> int
    decreases if b == 0 { 0 } else { b }
{
    if b == 0 { a } else { gcd(b, a % b) }
}

spec fn compute_answer(angle: int) -> int {
    let g = gcd(angle, 180int);
    let de_over_g = angle / g;
    let n180_over_g = 180int / g;
    if de_over_g == n180_over_g - 1 { n180_over_g * 2 } else { n180_over_g }
}

spec fn correct_output(angles: Seq<int>, result: Seq<int>) -> bool {
    valid_input(angles) ==> (
        result.len() == angles.len() &&
        forall|i: int| 0 <= i < angles.len() ==> (1 <= angles[i] < 180 ==> result[i] == compute_answer(angles[i]))
    )
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(angles: Seq<int>) -> (result: Seq<int>)
    requires valid_input(angles)
    ensures correct_output(angles, result)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}