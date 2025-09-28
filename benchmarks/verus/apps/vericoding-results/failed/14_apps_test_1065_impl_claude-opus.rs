// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, m: int, d: int) -> bool {
    2 <= n && 2 <= k <= n && 1 <= m <= n && 1 <= d <= n && m * d * k >= n
}

spec fn candies_used(x: int, d: int, k: int) -> int {
    x * ((d - 1) * k + 1)
}

spec fn valid_distribution(x: int, d: int, n: int, k: int, m: int, d_max: int) -> bool {
    1 <= x <= m && 1 <= d <= d_max && candies_used(x, d, k) <= n
}

spec fn person1_candies(x: int, d: int) -> int {
    x * d
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, m: i8, d: i8) -> (result: i8)
    requires valid_input(n as int, k as int, m as int, d as int)
    ensures
        result >= 0 &&
        result as int <= m as int * d as int &&
        (forall|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) ==> person1_candies(x, d_val) <= result as int) &&
        (exists|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) && person1_candies(x, d_val) == result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed initialization and arithmetic overflow checks */
    let mut max_candies: i8 = 0;
    let mut x: i8 = 1;
    
    // We need to find at least one valid distribution to establish invariants
    // Start with x=1, d=1 which gives candies_used = 1 * (0 * k + 1) = 1
    // This is valid since n >= 2, so we have a valid initial distribution
    if 1 <= n {  // candies_used(1, 1, k) = 1
        max_candies = 1;  // person1_candies(1, 1) = 1 * 1 = 1
    }
    
    // Now iterate through all possible distributions
    while x <= m
        invariant
            1 <= x,
            x <= m + 1,
            0 <= max_candies,
            max_candies <= m * d,
            forall|x_prev: int, d_val: int| 
                1 <= x_prev < x as int && valid_distribution(x_prev, d_val, n as int, k as int, m as int, d as int) 
                ==> person1_candies(x_prev, d_val) <= max_candies as int,
            exists|x_opt: int, d_opt: int| 
                valid_distribution(x_opt, d_opt, n as int, k as int, m as int, d as int) && 
                person1_candies(x_opt, d_opt) == max_candies as int,
        decreases m - x + 1
    {
        let mut d_val: i8 = 1;
        
        while d_val <= d
            invariant
                1 <= d_val,
                d_val <= d + 1,
                1 <= x,
                x <= m,
                0 <= max_candies,
                max_candies <= m * d,
                forall|x_prev: int, d_prev: int| 
                    ((1 <= x_prev < x as int && valid_distribution(x_prev, d_prev, n as int, k as int, m as int, d as int)) ||
                    (x_prev == x as int && 1 <= d_prev < d_val as int && valid_distribution(x_prev, d_prev, n as int, k as int, m as int, d as int)))
                    ==> person1_candies(x_prev, d_prev) <= max_candies as int,
                exists|x_opt: int, d_opt: int| 
                    valid_distribution(x_opt, d_opt, n as int, k as int, m as int, d as int) && 
                    person1_candies(x_opt, d_opt) == max_candies as int,
            decreases d - d_val + 1
        {
            // Compute candies_used(x, d_val, k) = x * ((d_val - 1) * k + 1)
            // Need to check for overflow at each step
            
            let mut valid_dist = false;
            
            // First compute (d_val - 1) * k
            if d_val == 1 {
                // (d_val - 1) * k = 0, so candies_used = x * 1 = x
                if x <= n {
                    valid_dist = true;
                }
            } else if k > 0 && d_val - 1 <= 127 / k {
                // Safe to compute (d_val - 1) * k
                let k_mult = (d_val - 1) * k;
                if k_mult < 127 {  // Need room for +1
                    let k_part = k_mult + 1;
                    // Now check if x * k_part is safe
                    if k_part > 0 && x <= 127 / k_part {
                        let candies_needed = x * k_part;
                        if candies_needed <= n {
                            valid_dist = true;
                        }
                    }
                }
            }
            
            if valid_dist {
                // Calculate person1_candies(x, d_val) = x * d_val
                if d_val > 0 && x <= 127 / d_val {
                    let person1_gets = x * d_val;
                    if person1_gets > max_candies {
                        max_candies = person1_gets;
                    }
                }
            }
            
            if d_val < d {
                d_val = d_val + 1;
            } else {
                d_val = d_val + 1;  // Exit condition
            }
        }
        
        if x < m {
            x = x + 1;
        } else {
            x = x + 1;  // Exit condition
        }
    }
    
    max_candies
}
// </vc-code>


}

fn main() {}