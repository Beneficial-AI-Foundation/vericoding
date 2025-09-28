// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, t: int) -> bool {
    1 <= n <= 10 && 0 <= t <= 10000
}

spec fn total_glasses(n: int) -> int {
    n * (n + 1) / 2
}

spec fn valid_result(result: int, n: int, t: int) -> bool {
    result >= 0 && result <= total_glasses(n)
}

spec fn correct_for_edge_cases(result: int, n: int, t: int) -> bool {
    (t == 0 ==> result == 0) &&
    (n == 1 && t >= 1 ==> result == 1) &&
    (n == 1 && t == 0 ==> result == 0) &&
    (t >= 1 && n > 1 ==> result >= 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, t: i8) -> (result: i8)
requires 
    valid_input(n as int, t as int)
ensures 
    valid_result(result as int, n as int, t as int),
    correct_for_edge_cases(result as int, n as int, t as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added overflow checks and fixed edge case handling */
    if t == 0 {
        return 0;
    }
    
    if n == 1 {
        // Special case: single glass
        if t >= 1 {
            return 1;
        } else {
            return 0;
        }
    }
    
    let mut level: i8 = 1;
    let mut full_count: i8 = 0;
    let mut total_needed: i8 = 0;
    
    while level <= n
        invariant
            1 <= level <= n + 1,
            0 <= full_count,
            full_count as int <= total_glasses(n as int),
            total_needed as int == (level - 1) * level / 2,
            full_count as int <= total_needed as int,
            total_needed >= 0,
            total_needed <= 55,
            level <= 10,
        decreases n + 1 - level
    {
        // Check for overflow before adding
        if total_needed as int + level as int > 127 {
            break;
        }
        
        let next_needed = total_needed + level;
        
        if next_needed <= t {
            // We have enough time to fill all glasses up to this level
            total_needed = next_needed;
            full_count = total_needed;
            
            // Check for overflow before incrementing
            if level < n {
                level = level + 1;
            } else {
                break;
            }
        } else {
            // Not enough time to fill all glasses at this level
            // Count partial glasses at current level
            let remaining = t - total_needed;
            if remaining > 0 {
                full_count = total_needed + remaining;
            }
            break;
        }
    }
    
    // Ensure we satisfy edge case requirements
    if t >= 1 && full_count == 0 {
        full_count = 1;
    }
    
    full_count
}
// </vc-code>


}

fn main() {}