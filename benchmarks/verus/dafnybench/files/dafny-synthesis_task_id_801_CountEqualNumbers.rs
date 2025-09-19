// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_equal_numbers(a: i8, b: i8, c: i8) -> (count: i8)
    ensures 
        count as int >= 0 && count as int <= 3,
        (count as int == 3) <==> (a as int == b as int && b as int == c as int),
        (count as int == 2) <==> ((a as int == b as int && b as int != c as int) || (a as int != b as int && b as int == c as int) || (a as int == c as int && b as int != c as int)),
        (count as int == 1) <==> (a as int != b as int && b as int != c as int && a as int != c as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}