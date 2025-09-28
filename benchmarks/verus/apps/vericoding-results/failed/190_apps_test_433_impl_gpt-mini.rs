// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int, a: int, b: int) -> bool {
        n >= 1 && 1 <= a <= n && -100 <= b <= 100
    }
    
    spec fn final_entrance(n: int, a: int, b: int) -> int {
        ((a - 1 + b) % n + n) % n + 1
    }
    
    spec fn valid_output(result: int, n: int) -> bool {
        1 <= result <= n
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): assert n >= 1 from valid_input */
fn input_n_positive(n: int, a: int, b: int)
    requires
        valid_input(n, a, b),
    ensures
        n >= 1,
{
    proof {
        assert(valid_input(n, a, b));
        assert(n >= 1);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int)
    ensures 
        valid_output(result as int, n as int),
        result as int == final_entrance(n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterative normalization of position with invariant linking to final_entrance */
{
    let mut cur: i8 = a;
    let mut rem: i32 = b as i32;
    while rem != 0
        invariant
            1 <= cur as int && cur as int <= n as int,
            cur as int == ((a as int - 1 + (b as int - rem as int)) % n as int + n as int) % n as int + 1,
        decreases (if rem > 0 { rem } else { -rem })
    {
        if rem > 0 {
            if cur == n { cur = 1; } else { cur = cur + 1; }
            rem -= 1;
        } else {
            if cur == 1 { cur = n; } else { cur = cur - 1; }
            rem += 1;
        }
    }
    let result = cur;
    proof {
        // From the loop invariant at termination (rem == 0) we get the desired equality
        assert(result as int == ((a as int - 1 + b as int) % n as int + n as int) % n as int + 1);
        assert(result as int == final_entrance(n as int, a as int, b as int));
        assert(1 <= result as int && result as int <= n as int);
    }
    result
}

// </vc-code>


}

fn main() {}