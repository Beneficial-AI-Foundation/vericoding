use vstd::prelude::*;

verus! {
/*
    i)  Write a verified method with signature

// <vc-helpers>
proof fn division_property(a: int, b: int, d: int)
    requires
        d != 0,
    ensures
        (a / d) * d <= a,
        ((a / d) + 1) * d > a,
{
}

proof fn no_division_by_zero(x: i32, y: i32)
    requires
        y == 42,
    ensures
        (42 - y as int) != 0,
{
    assert(42 - y as int == 0) by {
        assert(y as int == 42);
    };
}

proof fn safe_division(x: i32, y: i32)
    requires
        y != 42,
    ensures
        (42 - y as int) != 0,
{
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
        proof { 
            no_division_by_zero(x, y);
        }
        (0, true)
    } else {
        proof { 
            safe_division(x, y);
        }
        let divisor: int = 42 - y as int;
        proof { 
            division_property(x as int, y as int, divisor);
        }
        let result = (x as int / divisor) as i32;
        (result, false)
    }
}
// </vc-code>

fn main() {}

}