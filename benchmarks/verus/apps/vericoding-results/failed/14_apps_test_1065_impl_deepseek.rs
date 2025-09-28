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

proof fn lemma_candies_used_monotonic(x1: int, x2: int, d1: int, d2: int, k: int)
    requires
        1 <= x1 <= x2,
        1 <= d1 <= d2,
        2 <= k
    ensures
        candies_used(x1, d1, k) <= candies_used(x2, d2, k)
{
}

proof fn lemma_person1_candies_monotonic(x1: int, x2: int, d1: int, d2: int)
    requires
        1 <= x1 <= x2,
        1 <= d1 <= d2
    ensures
        person1_candies(x1, d1) <= person1_candies(x2, d2)
{
}

proof fn lemma_valid_distribution_exists(n: int, k: int, m: int, d_max: int)
    requires
        valid_input(n, k, m, d_max)
    ensures
        exists|x: int, d_val: int| valid_distribution(x, d_val, n, k, m, d_max)
{
}

proof fn lemma_max_candies_bound(n: int, k: int, m: int, d_max: int)
    requires
        valid_input(n, k, m, d_max)
    ensures
        forall|x: int, d_val: int| valid_distribution(x, d_val, n, k, m, d_max) ==> person1_candies(x, d_val) <= m * d_max
{
}

/* helper modified by LLM (iteration 4): Fixed proof function return type */
proof fn update_max_candies_ghost(max_candies_ghost: int, person1_candies_val: int) -> (new_max: int)
    ensures
        new_max >= max_candies_ghost,
        new_max >= person1_candies_val,
        new_max == if person1_candies_val > max_candies_ghost { person1_candies_val } else { max_candies_ghost }
{
    if person1_candies_val > max_candies_ghost {
        person1_candies_val
    } else {
        max_candies_ghost
    }
}

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
    /* code modified by LLM (iteration 4): Fixed type annotation for ghost variable */
    let mut max_candies: i8 = 0;
    let mut max_candies_ghost: int = 0;
    
    proof {
        let n_int = n as int;
        let k_int = k as int;
        let m_int = m as int;
        let d_int = d as int;
        
        lemma_valid_distribution_exists(n_int, k_int, m_int, d_int);
        lemma_max_candies_bound(n_int, k_int, m_int, d_int);
    }
    
    let mut d_val: i8 = 1;
    while d_val <= d
        invariant
            d_val >= 1,
            d_val <= d + 1,
            max_candies >= 0,
            max_candies <= m * d,
            max_candies as int == max_candies_ghost,
            forall|x: int, d_v: int| #![trigger] (d_v <= d_val as int - 1 && valid_distribution(x, d_v, n as int, k as int, m as int, d as int)) ==> person1_candies(x, d_v) <= max_candies_ghost,
            exists|x: int, d_v: int| #![trigger] (d_v <= d_val as int - 1 && valid_distribution(x, d_v, n as int, k as int, m as int, d as int) && person1_candies(x, d_v) == max_candies_ghost)
        decreases (d as int - d_val as int)
    {
        let mut x: i8 = 1;
        while x <= m
            invariant
                x >= 1,
                x <= m + 1,
                max_candies >= 0,
                max_candies <= m * d,
                max_candies as int == max_candies_ghost,
                forall|x2: int, d_v: int| #![trigger] (d_v <= d_val as int - 1 || (d_v == d_val as int && x2 <= x as int - 1 && valid_distribution(x2, d_v, n as int, k as int, m as int, d as int))) ==> person1_candies(x2, d_v) <= max_candies_ghost,
                exists|x2: int, d_v: int| #![trigger] (d_v <= d_val as int - 1 || (d_v == d_val as int && x2 <= x as int - 1 && valid_distribution(x2, d_v, n as int, k as int, m as int, d as int) && person1_candies(x2, d_v) == max_candies_ghost))
            decreases (m as int - x as int)
        {
            proof {
                let candies_needed = candies_used(x as int, d_val as int, k as int);
                if candies_needed <= n as int {
                    let person1_candies_val = person1_candies(x as int, d_val as int);
                    max_candies_ghost = update_max_candies_ghost(max_candies_ghost, person1_candies_val);
                }
            }
            x = x + 1;
        }
        proof {
            max_candies = max_candies_ghost as i8;
        }
        d_val = d_val + 1;
    }
    
    max_candies
}
// </vc-code>


}

fn main() {}