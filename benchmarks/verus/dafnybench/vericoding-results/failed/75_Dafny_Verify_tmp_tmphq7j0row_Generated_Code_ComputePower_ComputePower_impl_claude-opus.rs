use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}

// <vc-helpers>
proof fn power_strictly_increasing(n: nat)
    ensures power(n) < power(n + 1)
    decreases n
{
    // By definition: power(n + 1) = 2 * power(n)
    // Since power(n) >= 1 for all n, we have 2 * power(n) > power(n)
    reveal(power);
    if n == 0 {
        assert(power(0) == 1);
        assert(power(1) == 2 * power(0) == 2);
        assert(power(0) < power(1));
    } else {
        assert(power(n + 1) == 2 * power(n));
        assert(power(n) >= 1) by {
            power_positive(n);
        }
        assert(2 * power(n) > power(n));
    }
}

proof fn power_positive(n: nat)
    ensures power(n) >= 1
    decreases n
{
    if n == 0 {
        assert(power(0) == 1);
    } else {
        power_positive((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(power((n - 1) as nat) >= 1);
        assert(2 * power((n - 1) as nat) >= 2);
    }
}

proof fn power_bounds(n: nat)
    ensures n < 32 ==> power(n) <= 0x80000000
    decreases n
{
    if n >= 32 {
        return;
    }
    
    if n == 0 {
        assert(power(0) == 1);
        assert(1 <= 0x80000000);
    } else if n < 31 {
        power_bounds((n - 1) as nat);
        assert(power((n - 1) as nat) <= 0x80000000);
        assert(power(n) == 2 * power((n - 1) as nat));
        // Since n < 31, we have n - 1 < 30
        // We need to show that power(n-1) <= 0x40000000 to ensure 2*power(n-1) <= 0x80000000
        power_bound_half(n - 1);
        assert((n - 1) < 30 ==> power((n - 1) as nat) <= 0x40000000);
        if (n - 1) < 30 {
            assert(power((n - 1) as nat) <= 0x40000000);
            assert(2 * power((n - 1) as nat) <= 0x80000000);
        } else {
            assert(n - 1 == 30);
            assert(power(30) == 0x40000000) by {
                power_exact_30();
            }
            assert(2 * 0x40000000 == 0x80000000);
        }
    } else {
        assert(n == 31);
        assert(power(31) == 2 * power(30));
        assert(power(30) == 0x40000000) by {
            power_exact_30();
        }
        assert(2 * 0x40000000 == 0x80000000);
        assert(power(31) == 0x80000000);
    }
}

proof fn power_bound_half(n: nat)
    ensures n < 30 ==> power(n) <= 0x40000000
    decreases n
{
    if n >= 30 {
        return;
    }
    
    if n == 0 {
        assert(power(0) == 1);
        assert(1 <= 0x40000000);
    } else if n < 30 {
        power_bound_half((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
        if n - 1 < 29 {
            assert(power((n - 1) as nat) <= 0x40000000);
            assert(power((n - 1) as nat) <= 0x20000000) by {
                power_bound_quarter(n - 1);
            }
            assert(2 * power((n - 1) as nat) <= 0x40000000);
        } else {
            assert(n - 1 == 29);
            assert(power(29) == 0x20000000) by {
                power_exact_29();
            }
            assert(2 * 0x20000000 == 0x40000000);
        }
    }
}

proof fn power_bound_quarter(n: nat)
    ensures n < 29 ==> power(n) <= 0x20000000
    decreases n
{
    if n >= 29 {
        return;
    }
    
    if n == 0 {
        assert(power(0) == 1);
    } else if n <= 28 {
        power_bound_quarter((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(power((n - 1) as nat) <= 0x20000000);
        assert(power((n - 1) as nat) <= 0x10000000) by {
            if n - 1 < 28 {
                power_small_bound(n - 1);
            } else {
                assert(n - 1 == 28);
                power_exact_28();
            }
        }
        assert(2 * power((n - 1) as nat) <= 0x20000000);
    }
}

proof fn power_small_bound(n: nat)
    ensures n < 28 ==> power(n) <= 0x10000000
    decreases n
{
    if n >= 28 {
        return;
    }
    
    if n == 0 {
        assert(power(0) == 1);
    } else {
        power_small_bound((n - 1) as nat);
        assert(power(n) == 2 * power((n - 1) as nat));
        assert(power((n - 1) as nat) <= 0x10000000);
        assert(2 * power((n - 1) as nat) <= 0x20000000);
        assert(0x20000000 <= 0x10000000 || n < 28);
    }
}

proof fn power_exact_28()
    ensures power(28) == 0x10000000
{
    // 2^28 = 268435456 = 0x10000000
    calc! {
        ==
        power(28);
        2 * power(27);
        4 * power(26);
        8 * power(25);
        16 * power(24);
        32 * power(23);
        64 * power(22);
        128 * power(21);
        256 * power(20);
        512 * power(19);
        1024 * power(18);
        2048 * power(17);
        4096 * power(16);
        8192 * power(15);
        16384 * power(14);
        32768 * power(13);
        65536 * power(12);
        131072 * power(11);
        262144 * power(10);
        524288 * power(9);
        1048576 * power(8);
        2097152 * power(7);
        4194304 * power(6);
        8388608 * power(5);
        16777216 * power(4);
        33554432 * power(3);
        67108864 * power(2);
        134217728 * power(1);
        268435456 * power(0);
        268435456;
        0x10000000;
    }
}

proof fn power_exact_29()
    ensures power(29) == 0x20000000
{
    power_exact_28();
    assert(power(29) == 2 * power(28) == 2 * 0x10000000 == 0x20000000);
}

proof fn power_exact_30()
    ensures power(30) == 0x40000000
{
    power_exact_29();
    assert(power(30) == 2 * power(29) == 2 * 0x20000000 == 0x40000000);
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32, // practical bound to prevent overflow
    ensures p == power(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut p: u32 = 1;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            p == power(i as nat),
            n < 32,
            i < 31 ==> p <= 0x40000000,
            i <= 31 ==> p <= 0x80000000,
        decreases n - i,
    {
        proof {
            assert(i < n);
            assert(n < 32);
            assert(i < 31);
            power_bounds(i as nat);
            power_bound_half(i as nat);
            assert(power(i as nat) <= 0x40000000);
            assert(p == power(i as nat));
            assert(p <= 0x40000000);
            assert(2 * p <= 0x80000000);
        }
        
        p = 2 * p;
        i = i + 1;
        
        proof {
            assert(p == 2 * power((i - 1) as nat));
            assert(power(i as nat) == 2 * power((i - 1) as nat));
            assert(p == power(i as nat));
            
            if i < 31 {
                power_bound_half(i as nat);
                assert(power(i as nat) <= 0x40000000);
            } else {
                power_bounds(i as nat);
                assert(power(i as nat) <= 0x80000000);
            }
        }
    }
    
    proof {
        assert(i == n);
        assert(p == power(n as nat));
    }
    
    p
}
// </vc-code>

fn main() {
}

}