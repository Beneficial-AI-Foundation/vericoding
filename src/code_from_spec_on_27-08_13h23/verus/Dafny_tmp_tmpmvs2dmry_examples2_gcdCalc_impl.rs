use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
    recommends m > 0 && n > 0
    decreases m + n
    when m > 0 && n > 0
{
    if m == n {
        n
    } else if m > n {
        gcd(sub(m, n), n)
    } else {
        gcd(m, sub(n, m))
    }
}

spec fn exp_nat(base: nat, n: nat) -> nat
    decreases n
{
    if n == 0 {
        1nat
    } else if base == 0 {
        0nat
    } else {
        base * exp_nat(base, sub(n, 1))
    }
}

// <vc-helpers>
proof fn lemma_gcd_positive(m: nat, n: nat)
    requires m > 0, n > 0
    ensures gcd(m, n) > 0
    decreases m + n
{
    if m == n {
        assert(gcd(m, n) == n);
    } else if m > n {
        lemma_gcd_positive(m - n, n);
    } else {
        lemma_gcd_positive(m, n - m);
    }
}

proof fn lemma_gcd_decreases(m: nat, n: nat)
    requires m > 0, n > 0, m != n
    ensures if m > n { m - n + n < m + n } else { m + (n - m) < m + n }
{
    if m > n {
        assert(m - n + n < m + n);
    } else {
        assert(m + (n - m) < m + n);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn gcd_calc(m: u32, n: u32) -> (res: u32)
    requires m > 0 && n > 0
    ensures res == gcd(m as nat, n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn gcd_calc(m: u32, n: u32) -> (res: u32)
    requires m > 0, n > 0
    ensures res == gcd(m as nat, n as nat)
{
    let mut a: u32 = m;
    let mut b: u32 = n;
    while a != b
        invariant
            a > 0,
            b > 0,
            gcd(a as nat, b as nat) == gcd(m as nat, n as nat)
    {
        if a > b {
            a = a - b;
        } else {
            b = b - a;
        }
    }
    a
}
// </vc-code>

fn main() {}

}