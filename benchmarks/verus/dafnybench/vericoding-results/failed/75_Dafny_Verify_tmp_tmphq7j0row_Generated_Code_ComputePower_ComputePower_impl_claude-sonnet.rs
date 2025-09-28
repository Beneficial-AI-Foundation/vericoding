use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
proof fn lemma_power_bounds(n: nat)
    requires n < 32,
    ensures power(n) < 0x1_0000_0000,
    decreases n,
{
    if n == 0 {
        assert(power(0) == 1);
    } else if n == 1 {
        assert(power(1) == 2 * power(0));
        assert(power(1) == 2 * 1);
        assert(power(1) == 2);
    } else {
        lemma_power_bounds((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
        
        if n <= 31 {
            assert(power((n - 1) as nat) < 0x1_0000_0000);
            if n == 31 {
                lemma_power_exact_30();
                assert(power(30) == 0x4000_0000);
                assert(power(31) == 2 * 0x4000_0000);
                assert(power(31) == 0x8000_0000);
                assert(0x8000_0000 < 0x1_0000_0000);
            } else {
                assert(power((n - 1) as nat) <= 0x8000_0000 / 2);
                assert(2 * power((n - 1) as nat) <= 0x8000_0000);
                assert(0x8000_0000 < 0x1_0000_0000);
                assert(2 * power((n - 1) as nat) < 0x1_0000_0000);
            }
        }
    }
}

proof fn lemma_power_exact_30()
    ensures power(30) == 0x4000_0000,
{
    assert(power(0) == 1);
    assert(power(1) == 2);
    assert(power(2) == 4);
    assert(power(3) == 8);
    assert(power(4) == 16);
    assert(power(5) == 32);
    lemma_power_exact_10();
    assert(power(10) == 1024);
    lemma_power_multiplicative(10, 10);
    assert(power(20) == power(10) * power(10));
    assert(power(20) == 1024 * 1024);
    assert(power(20) == 0x10_0000);
    lemma_power_multiplicative(20, 10);
    assert(power(30) == power(20) * power(10));
    assert(power(30) == 0x10_0000 * 1024);
    assert(power(30) == 0x4000_0000);
}

proof fn lemma_power_exact_10()
    ensures power(10) == 1024,
{
    assert(power(0) == 1);
    assert(power(1) == 2);
    assert(power(2) == 4);
    assert(power(3) == 8);
    assert(power(4) == 16);
    assert(power(5) == 32);
    assert(power(6) == 64);
    assert(power(7) == 128);
    assert(power(8) == 256);
    assert(power(9) == 512);
    assert(power(10) == 1024);
}

proof fn lemma_power_multiplicative(a: nat, b: nat)
    ensures power(a + b) == power(a) * power(b),
    decreases a,
{
    if a == 0 {
        assert(power(0) == 1);
        assert(power(0 + b) == power(b));
        assert(power(0) * power(b) == 1 * power(b));
        assert(1 * power(b) == power(b));
    } else {
        lemma_power_multiplicative((a - 1) as nat, b);
        assert(power((a - 1) as nat + b) == power((a - 1) as nat) * power(b));
        assert(power(a + b) == 2 * power((a + b - 1) as nat));
        assert((a + b - 1) as nat == (a - 1) as nat + b);
        assert(power(a + b) == 2 * power((a - 1) as nat + b));
        assert(power(a + b) == 2 * (power((a - 1) as nat) * power(b)));
        assert(power(a + b) == (2 * power((a - 1) as nat)) * power(b));
        assert(power(a) == 2 * power((a - 1) as nat));
        assert(power(a + b) == power(a) * power(b));
    }
}

proof fn lemma_power_monotonic(i: nat, n: nat)
    requires i <= n,
    ensures power(i) <= power(n),
    decreases n - i,
{
    if i == n {
    } else {
        lemma_power_monotonic(i, (n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(power(i) <= power((n - 1) as nat));
        assert(power(i) <= 2 * power((n - 1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32, // practical bound to prevent overflow
    ensures p == power(n as nat),
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_power_bounds(n as nat);
    }
    
    let mut result: u32 = 1;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            i <= 32,
            n < 32,
            result == power(i as nat),
            power(n as nat) < 0x1_0000_0000,
            result < 0x1_0000_0000,
        decreases n - i,
    {
        proof {
            assert(i < n);
            assert(i < 32);
            assert((i + 1) <= n);
            assert((i + 1) <= 32);
            if (i + 1) < 32 {
                lemma_power_bounds((i + 1) as nat);
            }
            assert(power((i + 1) as nat) < 0x1_0000_0000);
            assert(power((i + 1) as nat) == 2 * power(i as nat));
            assert(2 * power(i as nat) < 0x1_0000_0000);
            assert(2 * result < 0x1_0000_0000);
        }
        
        result = result * 2;
        i = i + 1;
        
        proof {
            assert(power(i as nat) == 2 * power((i - 1) as nat));
            assert(result == 2 * power((i - 1) as nat));
            assert(result == power(i as nat));
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}