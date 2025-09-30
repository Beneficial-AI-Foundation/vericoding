// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_brother_numbers(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3 && a != b
}

spec fn late_brother(a: int, b: int) -> int
    recommends valid_brother_numbers(a, b)
{
    6 - a - b
}

spec fn is_valid_result(a: int, b: int, result: int) -> bool {
    valid_brother_numbers(a, b) ==> 
        (1 <= result <= 3 && result != a && result != b)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_brother_numbers(a as int, b as int)
    ensures 
        is_valid_result(a as int, b as int, result as int) &&
        result as int == late_brother(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    let res: i8 = 6i8 - a - b;

    if a == 1i8 {
        if b == 2i8 {
            assert(res as int == 6 - a as int - b as int);
            assert(1 <= res as int && res as int <= 3);
            assert(res as int != a as int);
            assert(res as int != b as int);
        } else if b == 3i8 {
            assert(res as int == 6 - a as int - b as int);
            assert(1 <= res as int && res as int <= 3);
            assert(res as int != a as int);
            assert(res as int != b as int);
        } else {
            // unreachable given precondition
        }
    } else if a == 2i8 {
        if b == 1i8 {
            assert(res as int == 6 - a as int - b as int);
            assert(1 <= res as int && res as int <= 3);
            assert(res as int != a as int);
            assert(res as int != b as int);
        } else if b == 3i8 {
            assert(res as int == 6 - a as int - b as int);
            assert(1 <= res as int && res as int <= 3);
            assert(res as int != a as int);
            assert(res as int != b as int);
        } else {
            // unreachable given precondition
        }
    } else {
        if b == 1i8 {
            assert(res as int == 6 - a as int - b as int);
            assert(1 <= res as int && res as int <= 3);
            assert(res as int != a as int);
            assert(res as int != b as int);
        } else if b == 2i8 {
            assert(res as int == 6 - a as int - b as int);
            assert(1 <= res as int && res as int <= 3);
            assert(res as int != a as int);
            assert(res as int != b as int);
        } else {
            // unreachable given precondition
        }
    }

    assert(late_brother(a as int, b as int) == 6 - a as int - b as int);
    res
}
// </vc-code>


}

fn main() {}