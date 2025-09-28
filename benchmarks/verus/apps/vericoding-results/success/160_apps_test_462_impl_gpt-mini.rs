// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x1: int, x2: int, x3: int) -> bool {
    1 <= x1 <= 100 && 1 <= x2 <= 100 && 1 <= x3 <= 100 &&
    x1 != x2 && x1 != x3 && x2 != x3
}

spec fn min_total_distance(x1: int, x2: int, x3: int) -> int
    recommends valid_input(x1, x2, x3)
{
    let max_pos = if x1 >= x2 && x1 >= x3 { x1 }
                  else if x2 >= x1 && x2 >= x3 { x2 }
                  else { x3 };
    let min_pos = if x1 <= x2 && x1 <= x3 { x1 }
                  else if x2 <= x1 && x2 <= x3 { x2 }
                  else { x3 };
    max_pos - min_pos
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): identity helper for ints */
spec fn id_int(x: int) -> int { x }
// </vc-helpers>

// <vc-spec>
fn find_minimum_total_distance(x1: i8, x2: i8, x3: i8) -> (result: i8)
    requires 
        valid_input(x1 as int, x2 as int, x3 as int)
    ensures 
        result as int == min_total_distance(x1 as int, x2 as int, x3 as int),
        result >= 1 && result <= 99
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute using i8 and prove equality with spec */
    let max_pos: i8 = if x1 >= x2 && x1 >= x3 { x1 }
                      else if x2 >= x1 && x2 >= x3 { x2 }
                      else { x3 };
    let min_pos: i8 = if x1 <= x2 && x1 <= x3 { x1 }
                      else if x2 <= x1 && x2 <= x3 { x2 }
                      else { x3 };
    let result: i8 = max_pos - min_pos;

    proof {
        let a = x1 as int;
        let b = x2 as int;
        let c = x3 as int;
        let max_pos_int = if a >= b && a >= c { a }
                          else if b >= a && b >= c { b }
                          else { c };
        let min_pos_int = if a <= b && a <= c { a }
                          else if b <= a && b <= c { b }
                          else { c };
        let result_int = max_pos_int - min_pos_int;
        assert(result as int == result_int);
        assert(result_int == min_total_distance(a, b, c));
        assert(1 <= result as int);
        assert(result as int <= 99);
    }

    result
}
// </vc-code>


}

fn main() {}