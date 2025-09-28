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
fn count_divisors_exec(n: usize) -> (count: usize)
    requires
        n > 0,
    ensures
        count == count_divisors(n as int),
{
    let mut cnt: usize = 0;
    let mut i: usize = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            cnt as int == Set::new(|d: int| 1 <= d < i as int && (n as int) % (d as int) == 0).len(),
        decreases n - i,
    {
        if n % i == 0 {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

/**
    Function to count special divisors.
*/
fn count_special_divisors_exec(n: usize) -> (count: usize)
    requires
        n > 0,
    ensures
        count == count_special_divisors(n as nat),
{
    let mut cnt: usize = 0;
    let mut i: usize = 2;
    while i <= n
        invariant
            2 <= i <= n + 1,
            cnt as int == Set::new(|d: int| 2 <= d < i as int && (n as int) % (d as int) == 0 && ((reduce_by_divisor(n as nat, d as nat) as int - 1) % (d as int) == 0)).len(),
        decreases n - i,
    {
        if n % i == 0 {
            let reduced_val: usize = if n >= i { n / i } else { n };
            if (reduced_val - 1) % i == 0 {
                cnt += 1;
            }
        }
        i += 1;
    }
    cnt
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
    /* code modified by LLM (iteration 2): Implemented solve function with proper casting to usize for helpers */
    if n == 1 {
        -1
    } else {
        let nn_usize: usize = n as usize;
        let c1 = count_divisors_exec(nn_usize - 1);
        let c2 = count_special_divisors_exec(nn_usize);
        (c1 as i8 + c2 as i8 - 1)
    }
}
// </vc-code>


}

fn main() {}