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
/* helper modified by LLM (iteration 5): fixed unclosed delimiter in Set constructor */
fn count_divisors_impl(n: int) -> (count: nat)
    requires
        n > 0,
    ensures
        count == count_divisors(n),
{
    let mut count: nat = 0;
    let mut i: int = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            count == Set::new(|d: int| 1 <= d < i && n % d == 0).len(),
        decreases n - i,
    {
        if n % i == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

/* helper modified by LLM (iteration 5): fixed unclosed delimiter in Set constructor */
fn count_special_divisors_impl(n: nat) -> (count: nat)
    requires
        n > 0,
    ensures
        count == count_special_divisors(n),
{
    let mut count: nat = 0;
    let mut i: int = 2;
    while i <= n as int
        invariant
            2 <= i <= n as int + 1,
            count == Set::new(|d: int| 2 <= d < i && (n as int) % d == 0 && ((reduce_by_divisor(n, d as nat) as int - 1) % d == 0)).len(),
        decreases n as int - i,
    {
        if (n as int) % i == 0 {
            let reduced = reduce_by_divisor(n, i as nat);
            if (reduced as int - 1) % i == 0 {
                count = count + 1;
            }
        }
        i = i + 1;
    }
    count
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
/* code modified by LLM (iteration 5): no changes needed to main logic */
{
    if n == 1 {
        -1
    } else {
        let divisors_minus_one = count_divisors_impl(n as int - 1) as i8;
        let special_divisors = count_special_divisors_impl(n as nat) as i8;
        divisors_minus_one + special_divisors - 1
    }
}
// </vc-code>


}

fn main() {}