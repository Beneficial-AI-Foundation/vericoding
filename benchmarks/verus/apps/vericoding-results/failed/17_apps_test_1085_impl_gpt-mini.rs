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
/* helper modified by LLM (iteration 5): runtime count divisors using u8 */
fn count_divisors_runtime(n: u8) -> u8
    requires
        n > 0,
    ensures
        result as nat == count_divisors(n as int),
{
    let mut i: u8 = 1;
    let mut cnt: u8 = 0;
    while i <= n
        invariant
            1 <= (i as int) <= (n as int) + 1,
            cnt as nat == Set::new(|d: int| 1 <= d <= (i as int) - 1 && (n as int) % d == 0).len(),
        decreases (n as nat) + 1 - (i as nat)
    {
        if n % i == 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}

/* helper modified by LLM (iteration 5): runtime count special divisors using u8 */
fn count_special_divisors_runtime(n: u8) -> u8
    requires
        n > 0,
    ensures
        result as nat == count_special_divisors(n as nat),
{
    let mut i: u8 = 2;
    let mut cnt: u8 = 0;
    while i <= n
        invariant
            2 <= (i as int) <= (n as int) + 1,
            cnt as nat == Set::new(|d: int| 2 <= d <= (i as int) - 1 && (n as int) % d == 0 && ((reduce_by_divisor(n as nat, d as nat) as int) - 1) % d == 0).len(),
        decreases (n as nat) + 1 - (i as nat)
    {
        let r: u8 = if n > 0 && i > 1 && n % i == 0 && n >= i { n / i } else { n };
        if n % i == 0 && (r - 1) % i == 0 {
            cnt = cnt + 1;
        }
        i = i + 1;
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
    /* code modified by LLM (iteration 5): compute using u8 runtime helpers and bind result variable for verification */
    let mut result: i8 = -1i8;
    if n == 1 {
        result = -1i8;
    } else {
        let n_minus1: u8 = n - 1;
        let cd: u8 = count_divisors_runtime(n_minus1);
        let cs: u8 = count_special_divisors_runtime(n);
        let val_i16: i16 = (cd as i16) + (cs as i16) - 1;
        result = val_i16 as i8;
    }
    result
}
// </vc-code>


}

fn main() {}