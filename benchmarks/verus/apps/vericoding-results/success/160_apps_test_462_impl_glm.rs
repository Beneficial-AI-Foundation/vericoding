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
fn min3(a: int, b: int, c: int) -> (result: int)
    ensures result == if a <= b && a <= c { a } else if b <= a && b <= c { b } else { c }
{
    if a <= b && a <= c {
        a
    } else if b <= a && b <= c {
        b
    } else {
        c
    }
}

fn max3(a: int, b: int, c: int) -> (result: int)
    ensures result == if a >= b && a >= c { a } else if b >= a && b >= c { b } else { c }
{
    if a >= b && a >= c {
        a
    } else if b >= a && b >= c {
        b
    } else {
        c
    }
}
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
    /* code modified by LLM (iteration 2): use spec functions directly to avoid int type issues */
    let max_val = if x1 >= x2 && x1 >= x3 { x1 } else if x2 >= x1 && x2 >= x3 { x2 } else { x3 };
    let min_val = if x1 <= x2 && x1 <= x3 { x1 } else if x2 <= x1 && x2 <= x3 { x2 } else { x3 };
    max_val - min_val
}
// </vc-code>


}

fn main() {}