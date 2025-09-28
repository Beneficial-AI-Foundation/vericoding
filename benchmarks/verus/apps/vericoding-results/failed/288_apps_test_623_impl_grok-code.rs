// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_valid_minutes(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
        0
    } else if a == 1 && b == 1 {
        0
    } else {
        (if a > 1 || b > 1 { 1 as int } else { 0 as int }) + 
        count_valid_minutes(
            if a < b { a + 1 } else { a - 2 }, 
            if a < b { b - 2 } else { b + 1 }
        )
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed pub from helper function to allow reference to spec function in ensures clause */
fn count_minutes(a: i8, b: i8) -> (res: i8)
    requires 
        a >= 0,
        b >= 0,
    ensures
        res >= 0,
        res as int == count_valid_minutes(a as int, b as int),
    decreases (a as int + b as int) + 1,
{
    if a <= 0 || b <= 0 {
        0
    } else if a == 1 && b == 1 {
        0
    } else {
        let add = if a > 1 || b > 1 { 1i8 } else { 0i8 };
        let next_a = if a < b { a + 1i8 } else { a - 2i8 };
        let next_b = if a < b { b - 2i8 } else { b + 1i8 };
        add + count_minutes(next_a, next_b)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8) -> (result: i8)
    requires 
        a1 >= 1 && a2 >= 1,
    ensures 
        result >= 0,
        result as int == count_valid_minutes(a1 as int, a2 as int),
        (a1 == 1 && a2 == 1) ==> result == 0,
// </vc-spec>
// <vc-code>
{
    count_minutes(a1, a2)
}
// </vc-code>


}

fn main() {}