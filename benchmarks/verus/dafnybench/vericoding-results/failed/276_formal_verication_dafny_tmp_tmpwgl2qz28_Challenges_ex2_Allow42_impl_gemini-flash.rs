use vstd::prelude::*;

verus! {
/*
    i)  Write a verified method with signature

// <vc-helpers>
#[macro_export]
macro_rules! vassert {
    ($($t:tt)*) => {
        verus! {
            assert($($t)*);
        }
    };
}
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
        // Prove that 42 - y is not zero
        proof {
            assert(42int - y as int != 0) by (nonlinear_arith); // This assertion is trivially true given y != 42
        }
        ((x as int / (42int - y as int)) as i32, false)
    }
}
// </vc-code>

fn main() {}

}