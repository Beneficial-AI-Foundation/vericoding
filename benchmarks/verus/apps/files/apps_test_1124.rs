// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(values: Seq<int>) -> bool {
    values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
}

spec fn gcd(a: int, b: int) -> int
    requires a > 0 && b > 0
    decreases if a >= b { a } else { b }
{
    if a == b { a }
    else if a > b { gcd(a - b, b) }
    else { gcd(a, b - a) }
}

spec fn gcd_seq(values: Seq<int>, index: int, current: int) -> int
    requires 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
    decreases values.len() - index
{
    if index == values.len() { current }
    else { gcd_seq(values, index + 1, gcd(current, values[index])) }
}

spec fn gcd_of_all(values: Seq<int>) -> int
    requires values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
{
    gcd_seq(values, 1, values[0])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(values: Seq<int>) -> (result: int)
    requires valid_input(values)
    ensures 
        result > 0 &&
        result == gcd_of_all(values) &&
        forall|i: int| 0 <= i < values.len() ==> values[i] % result == 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}