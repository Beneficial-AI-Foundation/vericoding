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
proof fn power_add(a: nat, b: nat)
    ensures power(a + b) == power(a) * power(b)
    decreases a
{
    if a == 0 {
        assert(power(0) == 1);
        assert(power(a + b) == power(b));
        assert(power(a) * power(b) == 1 * power(b) == power(b));
    } else {
        assert(power(a) == 2 * power((a - 1) as nat));
        power_add((a - 1) as nat, b);
        assert(power((a - 1) as nat + b) == power((a - 1) as nat) * power(b));
        assert(a + b == ((a - 1) as nat + b) + 1);
        assert(power(a + b) == power(((a - 1) as nat + b) + 1));
        assert(power(((a - 1) as nat + b) + 1) == 2 * power((a - 1) as nat + b));
        assert(power(a + b) == 2 * power((a - 1) as nat) * power(b));
        assert(power(a + b) == power(a) * power(b));
    }
}

proof fn power_invariant_helper(i: nat, n: nat, result: nat)
    requires result == power(i)
    ensures result * power((n - i) as nat) == power(n)
{
    power_add(i, (n - i) as nat);
    assert(i + (n - i) as nat == n);
}

proof fn power_bound(n: nat)
    ensures n <= 31 ==> power(n) <= u32::MAX
    decreases n
{
    if n == 0 {
        assert(power(0) == 1);
        assert(1 <= u32::MAX);
    } else if n <= 31 {
        if n == 31 {
            assert(power(31) == 2 * power(30));
            assert(power(30) == 1073741824);
            assert(power(31) == 2147483648);
            assert(2147483648 <= u32::MAX);
        } else {
            power_bound((n - 1) as nat);
            assert(power(n) == 2 * power((n - 1) as nat));
            assert(n - 1 <= 30);
            if n <= 30 {
                assert(power((n - 1) as nat) <= power(29));
                assert(power(29) == 536870912);
                assert(power((n - 1) as nat) <= u32::MAX / 2);
            }
        }
    }
}

proof fn power_31_exact()
    ensures power(31) == 2147483648
{
    assert(power(0) == 1);
    assert(power(1) == 2);
    assert(power(2) == 4);
    assert(power(3) == 8);
    assert(power(4) == 16);
    assert(power(5) == 32);
    assert(power(10) == 1024);
    assert(power(20) == 1048576);
    assert(power(30) == 1073741824);
    assert(power(31) == 2 * power(30));
    assert(power(31) == 2147483648);
}

proof fn power_32_overflow()
    ensures power(32) > u32::MAX
{
    power_31_exact();
    assert(power(32) == 2 * power(31));
    assert(power(32) == 2 * 2147483648);
    assert(power(32) == 4294967296);
    assert(u32::MAX == 4294967295);
    assert(power(32) > u32::MAX);
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    ensures p == power(n as nat)
// </vc-spec>
// <vc-code>
{
    if n >= 32 {
        proof {
            power_32_overflow();
            assert(n >= 32 ==> power(n as nat) >= power(32));
            assert(power(32) > u32::MAX);
            assert(power(n as nat) > u32::MAX);
            assert(false);
        }
        unreached()
    } else {
        let mut result: u32 = 1;
        let mut i: u32 = 0;
        
        while i < n
            invariant 
                i <= n,
                result == power(i as nat),
                i <= 31,
                n <= 31,
            decreases n - i
        {
            proof {
                power_bound(i as nat);
                assert(i < n && n <= 31);
                assert(i <= 30);
                assert(power(i as nat) <= power(30));
                assert(power(30) == 1073741824);
                assert(result <= 1073741824);
                assert(result * 2 <= 2147483648);
                assert(result * 2 <= u32::MAX);
            }
            
            result = result * 2;
            i = i + 1;
            
            proof {
                assert(result == 2 * power((i - 1) as nat));
                assert(power(i as nat) == 2 * power((i - 1) as nat));
                assert(result == power(i as nat));
            }
        }
        
        assert(i == n);
        assert(result == power(n as nat));
        result
    }
}
// </vc-code>

fn main() {
}

}