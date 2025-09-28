use vstd::prelude::*;

verus! {
/*
    i)  Write a verified method with signature

// <vc-helpers>
// (no helpers needed)
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
        let denom_int: int = 42int - (y as int);
        proof {
            assert(y != 42);
            assert(denom_int != 0);
        }
        let q_int: int = (x as int) / denom_int;
        let q: i32 = #[verifier::truncate] q_int as i32;
        proof {
            assert(q_int == (x as int) / (42int - y as int));
            assert(q == #[verifier::truncate] ((x as int) / (42int - y as int)) as i32);
        }
        (q, false)
    }
}
// </vc-code>

fn main() {}

}