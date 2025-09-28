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
/* helper modified by LLM (iteration 5): Fix syntax error by removing `ghost` keyword for `int` types in `lemma_recursion_relation` signature. */
proof fn lemma_recursion_relation(x: int, y: int)
    requires x >= 1 && y >= 1 && !(x==1 && y==1)
    ensures (if x < y { (x + 1) + (y - 2) } else { (x - 2) + (y + 1) }) < x + y
    decreases x + y
{
    if x < y {
        // Case 1: x < y
        // new_a = x + 1, new_b = y - 2
        // The sum of new_a and new_b is (x + 1) + (y - 2) = x + y - 1
        assert((x as int + 1) + (y as int - 2) == x as int + y as int - 1);
        assert(x as int + y as int - 1 < x as int + y as int);
    } else {
        // Case 2: x >= y (and x,y >= 1) means x-2 >= -1 and y+1 >= 2
        // new_a = x - 2, new_b = y + 1
        // The sum of new_a and new_b is (x - 2) + (y + 1) = x + y - 1
        assert((x as int - 2) + (y as int + 1) == x as int + y as int - 1);
        assert(x as int + y as int - 1 < x as int + y as int);
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
/* code modified by LLM (iteration 5): Add `decreases` clause and handle potential negative values in recursive call arguments. */
{
    let a = a1 as int;
    let b = a2 as int;

    if a <= 0 || b <= 0 {
        0
    } else if a == 1 && b == 1 {
        0
    } else {
        let na_val: i8;
        let nb_val: i8;

        if a < b {
            na_val = (a + 1) as i8;
            nb_val = (b - 2) as i8;
        } else {
            na_val = (a - 2) as i8;
            nb_val = (b + 1) as i8;
        }
        
        let recursive_result = if na_val < 1 || nb_val < 1 { 0 } else {
            solve(na_val, nb_val)
                decreases (a + b) as int
        };

        if a > 1 || b > 1 { (1 + recursive_result) as i8 } else { recursive_result as i8 }
    }
}
// </vc-code>


}

fn main() {}