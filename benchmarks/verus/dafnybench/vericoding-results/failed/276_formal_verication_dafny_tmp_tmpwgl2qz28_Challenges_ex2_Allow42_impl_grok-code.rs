use vstd::prelude::*;

verus! {
/*
    i)  Write a verified method with signature

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn allow_42(x: i32, y: i32) -> (ret: (i32, bool))
    ensures 
        (y != 42 ==> ret.0 == (x as int / (42int - y as int)) as i32 && ret.1 == false) &&
        (y == 42 ==> ret.0 == 0 && ret.1 == true)
// </vc-spec>
// <vc-code>
{
    let mut max_val: int = i32::MAX as int;
    let mut min_val: int = i32::MIN as int;
    let abs_x = vstd::math::abs(x as int);
    proof {
        assert(abs_x <= max_val);
        assert(-abs_x >= min_val);
    }

    if y == 42 {
        (0, true)
    } else {
        proof { assert(y != 42); }
        let denom_int = 42int - (y as int);
        proof { assert(denom_int != 0); }
        let res: int = (x as int) / denom_int;
        proof { assert(min_val <= res <= max_val); }
        let res_i32 = res as i32;
        (res_i32, false)
    }
}
// </vc-code>

fn main() {}

}