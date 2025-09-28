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
    if y == 42 {
        (0, true)
    } else {
        let denominator: i32 = 42 - y;
        assert(denominator != 0) by {
            assert(y != 42);
            assert(42 - y != 0);
        }
        let result = x / denominator;
        (result, false)
    }
}
// </vc-code>

fn main() {}

}