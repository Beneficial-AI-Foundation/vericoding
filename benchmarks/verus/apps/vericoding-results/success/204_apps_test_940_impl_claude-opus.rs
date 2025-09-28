// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn is_triangle(a: int, b: int, c: int) -> bool {
    a + b > c && a + c > b && b + c > a
}

spec fn min_operations_needed(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let max_val = if a >= b && a >= c { a } else if b >= c { b } else { c };
    let sum_of_other_two = a + b + c - max_val;
    if max_val - sum_of_other_two + 1 > 0 { max_val - sum_of_other_two + 1 } else { 0 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        result >= 0,
        result as int == min_operations_needed(a as int, b as int, c as int),
        (result as int == 0) <==> is_triangle(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fix triangle inequality check logic */
    let a32 = a as i32;
    let b32 = b as i32;
    let c32 = c as i32;
    
    let max_val = if a32 >= b32 && a32 >= c32 {
        a32
    } else if b32 >= c32 {
        b32
    } else {
        c32
    };
    
    let sum_others = (a32 + b32 + c32) - max_val;
    
    if max_val < sum_others {
        proof {
            assert(a as int + b as int > c as int);
            assert(a as int + c as int > b as int);
            assert(b as int + c as int > a as int);
            assert(is_triangle(a as int, b as int, c as int));
            assert(min_operations_needed(a as int, b as int, c as int) == 0);
        }
        0
    } else {
        let diff = max_val - sum_others;
        let result = (diff + 1) as i8;
        proof {
            assert(!is_triangle(a as int, b as int, c as int));
            assert(result as int == min_operations_needed(a as int, b as int, c as int));
        }
        result
    }
}
// </vc-code>


}

fn main() {}