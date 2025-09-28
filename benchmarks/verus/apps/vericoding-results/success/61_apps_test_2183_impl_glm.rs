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
proof fn lemma_late_brother_properties(a: int, b: int)
    requires valid_brother_numbers(a, b)
    ensures 
        1 <= late_brother(a, b) <= 3,
        late_brother(a, b) != a,
        late_brother(a, b) != b
{
    if a == 1 {
        if b == 2 {
            assert(late_brother(1,2) == 3);
            assert(3 != 1 && 3 != 2);
        } else {
            assert(b == 3);
            assert(late_brother(1,3) == 2);
            assert(2 != 1 && 2 != 3);
        }
    } else if a == 2 {
        if b == 1 {
            assert(late_brother(2,1) == 3);
            assert(3 != 2 && 3 != 1);
        } else {
            assert(b == 3);
            assert(late_brother(2,3) == 1);
            assert(1 != 2 && 1 != 3);
        }
    } else {
        assert(a == 3);
        if b == 1 {
            assert(late_brother(3,1) == 2);
            assert(2 != 3 && 2 != 1);
        } else {
            assert(b == 2);
            assert(late_brother(3,2) == 1);
            assert(1 != 3 && 1 != 2);
        }
    }
}
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
    let result = 6i8 - a - b;
    proof {
        lemma_late_brother_properties(a as int, b as int);
    }
    result
}
// </vc-code>


}

fn main() {}