// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(values: Seq<int>) -> bool {
    values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
}

spec fn gcd(a: int, b: int) -> int
    decreases (if a >= b { a } else { b }) when a > 0 && b > 0
{
    if a > 0 && b > 0 {
        if a == b {
            a
        } else if a > b {
            gcd(a - b, b)
        } else {
            gcd(a, b - a)
        }
    } else {
        1
    }
}

spec fn gcd_seq(values: Seq<int>, index: int, current: int) -> int
    decreases values.len() - index when 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
{
    if 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        if index == values.len() {
            current
        } else {
            gcd_seq(values, index + 1, gcd(current, values[index as int]))
        }
    } else {
        1
    }
}

spec fn gcd_of_all(values: Seq<int>) -> int {
    if values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        gcd_seq(values, 1, values[0])
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn values_as_int(values: Seq<i8>) -> Seq<int> {
    values.map(|i, x| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(values: Vec<i8>) -> (result: i8)
    requires valid_input(values_as_int(values@)) && values.len() <= 127
    ensures 
        result > 0 &&
        result as int == gcd_of_all(values_as_int(values@)) &&
        forall|i: int| 0 <= i < values@.len() ==> (values@[i] as int) % (result as int) == 0
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