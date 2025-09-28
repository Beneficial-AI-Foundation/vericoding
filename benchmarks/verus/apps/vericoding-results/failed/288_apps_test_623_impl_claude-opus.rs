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
    /* code modified by LLM (iteration 5): fix overflow and maintain invariants */
    if a1 == 1 && a2 == 1 {
        return 0;
    }
    
    let mut a = a1;
    let mut b = a2;
    let mut count: i8 = 0;
    
    while (a > 1 || b > 1) && a > 0 && b > 0 && count < 100
        invariant
            a >= 0,
            b >= 0,
            count >= 0,
            count <= 100,
            count as int + count_valid_minutes(a as int, b as int) == count_valid_minutes(a1 as int, a2 as int),
        decreases (if a > 0 && b > 0 { (a as int) + (b as int) } else { 0 })
    {
        let old_a = a;
        let old_b = b;
        
        if old_a < old_b {
            a = if old_a < 127 { old_a + 1 } else { 127 };
            b = if old_b >= 2 { old_b - 2 } else { 0 };
        } else {
            a = if old_a >= 2 { old_a - 2 } else { 0 };
            b = if old_b < 127 { old_b + 1 } else { 127 };
        }
        
        count = count + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}