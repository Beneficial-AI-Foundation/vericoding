// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: nat) -> bool {
    n > 0
}

spec fn reduce_by_divisor(n: nat, d: nat) -> nat {
    if n > 0 && d > 1 && n % d == 0 && n >= d {
        n / d
    } else {
        n
    }
}

spec fn count_divisors(n: int) -> nat {
    if n > 0 {
        Set::new(|d: int| 1 <= d <= n && n % d == 0).len()
    } else {
        0
    }
}

spec fn count_special_divisors(n: nat) -> nat {
    if n > 0 {
        Set::new(|d: int| 2 <= d <= n && (n as int) % d == 0 && ((reduce_by_divisor(n, d as nat) as int) - 1) % d == 0).len()
    } else {
        0
    }
}

spec fn count_valid_k_values(n: nat) -> int {
    if n > 0 {
        if n == 1 {
            -1
        } else {
            count_divisors(n as int - 1) as int + count_special_divisors(n) as int - 1
        }
    } else {
        -1
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: u8) -> (result: i8)
    requires 
        valid_input(n as nat)
    ensures 
        result as int == count_valid_k_values(n as nat),
        n == 1 ==> result as int == -1,
        n > 1 ==> result as int == count_divisors(n as int - 1) as int + count_special_divisors(n as nat) as int - 1,
        result as int >= -1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop bounds and arithmetic overflow issues */
    if n == 1 {
        return -1;
    }
    
    let mut count: i8 = 0;
    let mut k: u8 = 1;
    
    // Count divisors of n-1
    while k <= n - 1
        invariant
            n > 1,
            1 <= k <= n,
            count >= 0,
            count <= 127
        decreases (n as int) - (k as int)
    {
        if (n - 1) % k == 0 {
            if count < 127 {
                count = count + 1;
            }
        }
        if k < n - 1 {
            k = k + 1;
        } else {
            break;
        }
    }
    
    // Count special divisors of n
    k = 2;
    while k <= n
        invariant
            n > 1,
            2 <= k <= n + 1,
            count >= 0,
            count <= 127
        decreases (n as int) + 1 - (k as int)
    {
        if n % k == 0 {
            let temp1 = n / k;
            if temp1 >= 1 && (temp1 - 1) % k == 0 {
                if count < 127 {
                    count = count + 1;
                }
            }
        }
        if k < n {
            k = k + 1;
        } else {
            break;
        }
    }
    
    // Subtract 1 as per specification
    if count > 0 {
        count = count - 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}