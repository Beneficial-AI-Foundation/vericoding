use vstd::prelude::*;

verus! {
/*
    i)  Write a verified method with signature

// <vc-helpers>
fn diff_nonzero_when_y_not_42(x: i32, y: i32)
    requires y != 42
    ensures (42 as int - y as int) != 0
{
    assert(y != 42);
    assert((42 as int - y as int) != 0);
}

fn div_result_in_bounds(x: i32, y: i32)
    requires y != 42
    ensures ({
        let diff = 42 as int - y as int;
        let res = x as int / diff;
        res * res <= (x as int) * (x as int)
    })
{
    let diff = 42 as int - y as int;
    let res = x as int / diff;
    assert(res * res <= (x as int) * (x as int));
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
        proof {
            diff_nonzero_when_y_not_42(x, y);
            div_result_in_bounds(x, y);
        }
        let diff_int = 42 - y as int;
        let quotient_int = (x as int) / diff_int;
        (quotient_int as i32, false)
    }
}
// </vc-code>

fn main() {}

}