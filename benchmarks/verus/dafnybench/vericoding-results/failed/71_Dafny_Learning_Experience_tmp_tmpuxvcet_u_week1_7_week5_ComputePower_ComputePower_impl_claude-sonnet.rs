use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

fn calc_power(n: u32) -> (p: u32)
    ensures p == 2 * n
{
  assume(false);
  0
}

// <vc-helpers>
proof fn lemma_power_zero()
    ensures power(0) == 1
{
}

proof fn lemma_power_succ(n: nat)
    ensures power(n + 1) == 2 * power(n)
{
}

proof fn lemma_power_small(n: nat)
    requires n <= 31
    ensures power(n) <= 0x80000000
    decreases n
{
    if n == 0 {
        assert(power(0) == 1);
    } else {
        lemma_power_small((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(power((n - 1) as nat) <= 0x80000000);
        if n <= 30 {
            lemma_power_bounds((n - 1) as nat);
            assert(power((n - 1) as nat) <= 0x40000000);
            assert(power(n) == 2 * power((n - 1) as nat));
            assert(2 * power((n - 1) as nat) <= 2 * 0x40000000);
            assert(2 * 0x40000000 == 0x80000000);
            assert(power(n) <= 0x80000000);
        } else {
            assert(n == 31);
            lemma_power_bounds(30);
            assert(power(30) <= 0x40000000);
            assert(power(31) == 2 * power(30));
            assert(2 * power(30) <= 2 * 0x40000000);
            assert(2 * 0x40000000 == 0x80000000);
            assert(power(31) <= 0x80000000);
        }
    }
}

proof fn lemma_power_bounds(n: nat)
    requires n <= 30
    ensures power(n) <= 0x40000000
    decreases n
{
    if n == 0 {
        assert(power(0) == 1);
        assert(1 <= 0x40000000);
    } else {
        lemma_power_bounds((n - 1) as nat);
        assert(power((n - 1) as nat) <= 0x40000000);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(2 * power((n - 1) as nat) <= 2 * 0x40000000);
        assert(2 * 0x40000000 == 0x80000000);
        assert(0x80000000 <= 0x40000000 * 2);
        if n <= 29 {
            lemma_power_bounds((n - 1) as nat);
            assert(power((n - 1) as nat) <= 0x40000000);
            assert(power(n) == 2 * power((n - 1) as nat));
            if n <= 15 {
                assert(power(n) <= 0x40000000);
            } else {
                assert(power(n) <= 0x40000000);
            }
        } else {
            assert(n == 30);
            assert(power(30) == 0x40000000);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    ensures p == power(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        proof {
            lemma_power_zero();
        }
        1
    } else if n <= 31 {
        let mut result: u32 = 1;
        let mut i: u32 = 0;
        
        proof {
            assert(result == 1);
            assert(power(0) == 1);
            assert(result == power(i as nat));
        }
        
        while i < n
            invariant 
                i <= n,
                result == power(i as nat),
                n <= 31,
                result <= 0x80000000,
            decreases n - i
        {
            proof {
                lemma_power_succ(i as nat);
                assert(power((i + 1) as nat) == 2 * power(i as nat));
                assert(power((i + 1) as nat) == 2 * result);
                lemma_power_small((i + 1) as nat);
                assert(power((i + 1) as nat) <= 0x80000000);
                assert(2 * result <= 0x80000000);
            }
            result = result * 2;
            i = i + 1;
        }
        result
    } else {
        0
    }
}
// </vc-code>

fn main() {
}

}