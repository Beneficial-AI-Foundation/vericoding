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
/* helper modified by LLM (iteration 5): fixed incorrect path for arithmetic lemmas */
fn compute_count_divisors(n_exec: u64) -> (result: u64)
    requires
        n_exec > 0,
    ensures
        result as int == count_divisors(n_exec as int),
{
    let mut count: u64 = 0;
    let mut d: u64 = 1;
    while d <= n_exec
        invariant
            1 <= d <= n_exec + 1,
            n_exec > 0,
            count as int == Set::new(|i: int| 1 <= i < d && (n_exec as int) % i == 0).len(),
    {
        if n_exec % d == 0 {
            proof {
                vstd::arithmetic::div_mod::lemma_mod_is_mod(n_exec as int, d as int);
            }
            count = count + 1;
        }
        d = d + 1;
    }
    count
}

/* helper modified by LLM (iteration 5): fixed incorrect path for arithmetic lemmas */
fn compute_count_special_divisors(n_exec: u64) -> (result: u64)
    requires
        n_exec > 1,
    ensures
        result as nat == count_special_divisors(n_exec as nat),
{
    let mut count: u64 = 0;
    let mut d: u64 = 2;
    while d <= n_exec
        invariant
            2 <= d <= n_exec + 1,
            n_exec > 1,
            count as nat == Set::new(|i: int| 2 <= i < d && (n_exec as int) % i == 0 && ((reduce_by_divisor(n_exec as nat, i as nat) as int) - 1) % i == 0).len(),
    {
        if n_exec % d == 0 {
            proof {
                vstd::arithmetic::div_mod::lemma_mod_is_mod(n_exec as int, d as int);
            }
            let reduced_n = n_exec / d;
            if reduced_n > 0 && (reduced_n - 1) % d == 0 {
                proof {
                    vstd::arithmetic::div_mod::lemma_mod_is_mod((reduced_n - 1) as int, d as int);
                    let n_nat = n_exec as nat;
                    let d_nat = d as nat;
                    assert(d_nat > 1);
                    assert(n_nat % d_nat == 0);
                    assert(n_nat >= d_nat);
                    assert(reduce_by_divisor(n_nat, d_nat) == n_nat / d_nat);
                    assert(reduced_n as nat == n_nat / d_nat);
                    assert(reduced_n as nat == reduce_by_divisor(n_nat, d_nat));
                }
                count = count + 1;
            }
        }
        d = d + 1;
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
/* code modified by LLM (iteration 5): main fix for compilation was in helpers */
{
    if n == 1 {
        -1
    } else {
        let n_exec = n as u64;
        let n_minus_1_exec = (n - 1) as u64;

        let num_divs = compute_count_divisors(n_minus_1_exec);
        let num_special_divs = compute_count_special_divisors(n_exec);

        let result = num_divs + num_special_divs - 1;

        proof {
            assert(n_minus_1_exec as int == (n as int) - 1);
        }

        result as i8
    }
}
// </vc-code>


}

fn main() {}