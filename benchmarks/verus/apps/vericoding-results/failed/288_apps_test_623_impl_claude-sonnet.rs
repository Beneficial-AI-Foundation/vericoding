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
/* helper modified by LLM (iteration 5): strengthen bounded proof to show proper upper bound */
proof fn count_valid_minutes_decreases(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures
        a > 1 || b > 1 ==> (
            (if a < b { a + 1 } else { a - 2 }) + (if a < b { b - 2 } else { b + 1 }) < a + b
        )
{
    if a > 1 || b > 1 {
        if a < b {
            assert((a + 1) + (b - 2) == a + b - 1 < a + b);
        } else {
            assert((a - 2) + (b + 1) == a + b - 1 < a + b);
        }
    }
}

proof fn count_valid_minutes_nonneg(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures count_valid_minutes(a, b) >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
        assert(count_valid_minutes(a, b) == 0);
    } else if a == 1 && b == 1 {
        assert(count_valid_minutes(a, b) == 0);
    } else {
        let next_a = if a < b { a + 1 } else { a - 2 };
        let next_b = if a < b { b - 2 } else { b + 1 };
        count_valid_minutes_decreases(a, b);
        count_valid_minutes_nonneg(next_a, next_b);
    }
}

proof fn count_valid_minutes_bounded(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures count_valid_minutes(a, b) <= a + b
    decreases a + b
{
    if a <= 0 || b <= 0 {
        assert(count_valid_minutes(a, b) == 0);
    } else if a == 1 && b == 1 {
        assert(count_valid_minutes(a, b) == 0);
    } else {
        let next_a = if a < b { a + 1 } else { a - 2 };
        let next_b = if a < b { b - 2 } else { b + 1 };
        count_valid_minutes_decreases(a, b);
        count_valid_minutes_bounded(next_a, next_b);
        assert(count_valid_minutes(a, b) == 1 + count_valid_minutes(next_a, next_b));
        assert(count_valid_minutes(next_a, next_b) <= next_a + next_b);
        assert(next_a + next_b < a + b);
        assert(count_valid_minutes(a, b) <= 1 + (a + b - 1) == a + b);
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
    /* code modified by LLM (iteration 5): use proper bounded proof with a+b bound */
    proof {
        count_valid_minutes_nonneg(a1 as int, a2 as int);
        count_valid_minutes_bounded(a1 as int, a2 as int);
        assert(count_valid_minutes(a1 as int, a2 as int) <= (a1 as int) + (a2 as int));
        assert((a1 as int) + (a2 as int) <= 254);
    }
    
    if a1 == 1 && a2 == 1 {
        return 0;
    }
    
    let mut count = 0i8;
    let mut curr_a = a1;
    let mut curr_b = a2;
    
    while curr_a > 1 || curr_b > 1
        invariant
            curr_a >= 0,
            curr_b >= 0,
            count >= 0,
            count <= 127,
            curr_a <= 127,
            curr_b <= 127,
            count as int + count_valid_minutes(curr_a as int, curr_b as int) == count_valid_minutes(a1 as int, a2 as int),
        decreases curr_a + curr_b
    {
        proof {
            count_valid_minutes_decreases(curr_a as int, curr_b as int);
            count_valid_minutes_nonneg(curr_a as int, curr_b as int);
            count_valid_minutes_bounded(curr_a as int, curr_b as int);
            assert(count_valid_minutes(curr_a as int, curr_b as int) <= (curr_a as int) + (curr_b as int));
            assert(count as int <= 127);
            assert((curr_a as int) + (curr_b as int) <= 254);
        }
        
        let old_a = curr_a;
        let old_b = curr_b;
        
        if curr_a < curr_b {
            curr_a = curr_a + 1;
            curr_b = curr_b - 2;
        } else {
            curr_a = curr_a - 2;
            curr_b = curr_b + 1;
        }
        
        proof {
            assert(count_valid_minutes(old_a as int, old_b as int) == 
                   1 + count_valid_minutes(curr_a as int, curr_b as int));
            assert(count_valid_minutes(curr_a as int, curr_b as int) <= (curr_a as int) + (curr_b as int));
            assert((curr_a as int) + (curr_b as int) < (old_a as int) + (old_b as int));
            assert(count < 127);
        }
        
        count = count + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}