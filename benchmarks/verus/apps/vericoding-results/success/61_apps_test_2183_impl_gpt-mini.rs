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
/* helper modified by LLM (iteration 3): properties of late_brother proved by case analysis */
proof fn late_brother_props(a: int, b: int)
    requires
        valid_brother_numbers(a,b),
    ensures
        1 <= late_brother(a,b) <= 3 && late_brother(a,b) != a && late_brother(a,b) != b,
{
    let r = late_brother(a,b);
    assert(r == 6 - a - b);
    if a == 1 {
        if b == 2 {
            assert(r == 3);
        } else {
            assert(b == 3);
            assert(r == 2);
        }
    } else if a == 2 {
        if b == 1 {
            assert(r == 3);
        } else {
            assert(b == 3);
            assert(r == 1);
        }
    } else {
        if b == 1 {
            assert(r == 2);
        } else {
            assert(b == 2);
            assert(r == 1);
        }
    }
    assert(1 <= r && r <= 3);
    assert(r != a && r != b);
}

/* helper modified by LLM (iteration 3): int to i8 roundtrip proof for values 1..3 */
proof fn int_to_i8_roundtrip_small(v: int)
    requires
        1 <= v <= 3,
    ensures
        (v as i8) as int == v,
{
    if v == 1 {
        assert((v as i8) as int == 1);
    } else if v == 2 {
        assert((v as i8) as int == 2);
    } else {
        assert(v == 3);
        assert((v as i8) as int == 3);
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
    /* code modified by LLM (iteration 3): compute result by case analysis without using 'int' in executable code */
    let result: i8;
    if a == 1 {
        if b == 2 {
            result = 3;
        } else {
            result = 2;
        }
    } else if a == 2 {
        if b == 1 {
            result = 3;
        } else {
            result = 1;
        }
    } else {
        if b == 1 {
            result = 2;
        } else {
            result = 1;
        }
    }
    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        late_brother_props(ai, bi);
        let ri: int = late_brother(ai, bi);
        if a == 1 {
            if b == 2 {
                assert(result == 3);
                assert(ri == 3);
            } else {
                assert(b == 3);
                assert(result == 2);
                assert(ri == 2);
            }
        } else if a == 2 {
            if b == 1 {
                assert(result == 3);
                assert(ri == 3);
            } else {
                assert(b == 3);
                assert(result == 1);
                assert(ri == 1);
            }
        } else {
            if b == 1 {
                assert(result == 2);
                assert(ri == 2);
            } else {
                assert(b == 2);
                assert(result == 1);
                assert(ri == 1);
            }
        }
        int_to_i8_roundtrip_small(ri);
        assert((result as int) == ri);
    }
    result
}

// </vc-code>


}

fn main() {}