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
/* helper modified by LLM (iteration 3): fixed invariant block syntax and added decreases clause */
fn count_divisors_exec(n: int) -> (result: nat)
    ensures result == count_divisors(n)
{
    if n <= 0 {
        0
    } else {
        let mut count = 0;
        let mut i = 1;
        while i <= n
            invariant
                1 <= i <= n+1,
                count == Set::<int>::new(|d: int| 1<=d<=i-1 && n % d == 0).len(),
            decreases n - i
        {
            if n % i == 0 {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

/* helper modified by LLM (iteration 3): fixed invariant block syntax and added decreases clause */
fn count_special_divisors_exec(n: nat) -> (result: nat)
    ensures result == count_special_divisors(n)
{
    if n == 0 {
        0
    } else {
        let mut count = 0;
        let mut d = 2;
        while d <= n
            invariant
                2 <= d <= n+1,
                count == Set::<int>::new(|k: int| 2<=k<=d-1 && (n as int) % k == 0 && (((n as int) / k - 1) % k == 0)).len(),
            decreases n - d
        {
            if (n as int) % d == 0 {
                let m_int = (n as int) / d;
                if (m_int - 1) % d == 0 {
                    count += 1;
                }
            }
            d += 1;
        }
        count
    }
}
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
    /* code modified by LLM (iteration 3): updated to use fixed helper functions */
    let n_nat = n as nat;
    if n_nat == 1 {
        -1 as i8
    } else {
        let n_minus_one = (n as int) - 1;
        let count_div = count_divisors_exec(n_minus_one);
        let count_special = count_special_divisors_exec(n_nat);
        let total = count_div as int + count_special as int - 1;
        total as i8
    }
}
// </vc-code>


}

fn main() {}