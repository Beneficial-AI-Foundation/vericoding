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

// </vc-helpers>

// <vc-spec>
fn any_int(x: i8, y: i8, z: i8) -> (result: bool)
    ensures valid_result(x as int, y as int, z as int, result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i32 for arithmetic to avoid int type in exec context */
    let x_i32 = x as i32;
    let y_i32 = y as i32;
    let z_i32 = z as i32;
    
    let result = (x_i32 == y_i32 + z_i32) || 
                 (y_i32 == x_i32 + z_i32) || 
                 (z_i32 == x_i32 + y_i32);
    
    proof {
        assert(all_integers(x as int, y as int, z as int));
        assert(x as int == x_i32 as int);
        assert(y as int == y_i32 as int);
        assert(z as int == z_i32 as int);
        assert(result <==> one_equals_sum_of_other_two(x as int, y as int, z as int));
        assert(valid_result(x as int, y as int, z as int, result));
    }
    
    result
}
// </vc-code>


}

fn main() {}