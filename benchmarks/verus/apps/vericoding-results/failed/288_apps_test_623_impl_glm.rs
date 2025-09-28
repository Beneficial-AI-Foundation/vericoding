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
    let mut count: int = 0;
    let mut x: int = a1 as int;
    let mut y: int = a2 as int;

    while !( (x <= 0 || y <= 0) || (x == 1 && y == 1) )
        invariant
            x > 0,
            y > 0,
            (x, y) != (1,1),
            count + count_valid_minutes(x, y) == count_valid_minutes(a1 as int, a2 as int),
        decreases (x+y) as nat
    {
        count += 1;
        if x < y {
            x = x + 1;
            y = y - 2;
        } else {
            x = x - 2;
            y = y + 1;
        }
    }

    count as i8
}
// </vc-code>


}

fn main() {}