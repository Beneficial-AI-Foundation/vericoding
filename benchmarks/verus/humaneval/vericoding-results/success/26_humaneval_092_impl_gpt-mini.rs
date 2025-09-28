// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_integer(x: int) -> bool {
    true
}

spec fn all_integers(x: int, y: int, z: int) -> bool {
    is_integer(x) && is_integer(y) && is_integer(z)
}

spec fn one_equals_sum_of_other_two(x: int, y: int, z: int) -> bool {
    x == y + z || y == x + z || z == x + y
}

spec fn valid_result(x: int, y: int, z: int, result: bool) -> bool {
    result <==> (all_integers(x, y, z) && one_equals_sum_of_other_two(x, y, z))
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): preserve equality when casting i8 to int */
proof fn i8_eq_cast_preserve(x: i8, y: i8) ensures (x == y) <==> (x as int == y as int) {
    if x == y {
        assert(x as int == y as int);
    } else {
        assert(!(x as int == y as int));
    }
}

/* helper modified by LLM (iteration 3): preserve addition when casting i8->i16->int */
proof fn i8_add_cast_preserve(x: i8, y: i8, z: i8) ensures (x as i16 == y as i16 + z as i16) <==> (x as int == y as int + z as int) {
    // cast from i8 to i16 then to int matches direct cast to int
    assert(((x as i16) as int) == (x as int));
    assert(((y as i16) as int) == (y as int));
    assert(((z as i16) as int) == (z as int));
    // addition preserved when casting the i16-sum to int
    assert(((y as i16 + z as i16) as int) == ((y as i16) as int + (z as i16) as int));
    // equivalences step-by-step
    assert((x as i16 == y as i16 + z as i16) <==> (((x as i16) as int) == ((y as i16 + z as i16) as int)));
    assert((((x as i16) as int) == ((y as i16 + z as i16) as int)) <==> ((x as int) == ((y as i16) as int + (z as i16) as int)));
    assert(((y as i16) as int + (z as i16) as int) == (y as int + z as int));
    assert((x as int == ((y as i16) as int + (z as i16) as int)) <==> (x as int == (y as int + z as int)));
}

// </vc-helpers>

// <vc-spec>
fn any_int(x: i8, y: i8, z: i8) -> (result: bool)
    ensures valid_result(x as int, y as int, z as int, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute result using i16 and prove equivalence to spec */
    let result = (x as i16 == y as i16 + z as i16) || (y as i16 == x as i16 + z as i16) || (z as i16 == x as i16 + y as i16);
    proof {
        let a = x as int;
        let b = y as int;
        let c = z as int;
        assert(is_integer(a));
        assert(is_integer(b));
        assert(is_integer(c));
        assert(all_integers(a, b, c));
        i8_add_cast_preserve(x, y, z);
        i8_add_cast_preserve(y, x, z);
        i8_add_cast_preserve(z, x, y);
        assert((x as i16 == y as i16 + z as i16) <==> (a == b + c));
        assert((y as i16 == x as i16 + z as i16) <==> (b == a + c));
        assert((z as i16 == x as i16 + y as i16) <==> (c == a + b));
        assert(result == (a == b + c || b == a + c || c == a + b));
        assert(result <==> one_equals_sum_of_other_two(a, b, c));
        assert(result <==> (all_integers(a, b, c) && one_equals_sum_of_other_two(a, b, c)));
    }
    result
}

// </vc-code>


}

fn main() {}