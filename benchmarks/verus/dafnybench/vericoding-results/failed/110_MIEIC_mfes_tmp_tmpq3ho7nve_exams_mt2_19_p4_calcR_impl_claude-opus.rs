use vstd::prelude::*;

verus! {

spec fn R(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        0nat 
    } else if R((n-1) as nat) > n { 
        (R((n-1) as nat) - n) as nat
    } else { 
        (R((n-1) as nat) + n) as nat
    }
}

// <vc-helpers>
proof fn R_bounded(n: nat)
    ensures R(n) <= n * (n + 1) / 2
    decreases n
{
    if n == 0 {
        assert(R(0) == 0);
        assert(0 <= 0 * 1 / 2);
    } else {
        R_bounded((n - 1) as nat);
        let prev = R((n - 1) as nat);
        assert(prev <= (n - 1) * n / 2);
        
        if prev > n {
            assert(R(n) == (prev - n) as nat);
            assert(R(n) < prev);
            assert(prev <= (n - 1) * n / 2);
            assert(R(n) < (n - 1) * n / 2);
            assert((n - 1) * n / 2 <= n * (n + 1) / 2) by {
                assert((n - 1) * n == n * (n - 1));
                assert(n * (n - 1) == n * n - n);
                assert(n * (n + 1) == n * n + n);
                assert((n - 1) * n / 2 + n == n * (n + 1) / 2);
            }
            assert(R(n) <= n * (n + 1) / 2);
        } else {
            assert(R(n) == prev + n);
            assert(prev <= (n - 1) * n / 2);
            assert(R(n) == prev + n);
            assert(R(n) <= (n - 1) * n / 2 + n);
            assert((n - 1) * n / 2 + n == n * (n + 1) / 2) by {
                assert((n - 1) * n == n * (n - 1));
                assert(n * (n - 1) == n * n - n);
                assert((n - 1) * n + 2 * n == n * n - n + 2 * n);
                assert(n * n - n + 2 * n == n * n + n);
                assert(((n - 1) * n + 2 * n) / 2 == (n * n + n) / 2);
                assert((n - 1) * n / 2 + n == (n * n + n) / 2);
                assert((n * n + n) / 2 == n * (n + 1) / 2);
            }
            assert(R(n) <= n * (n + 1) / 2);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut r: u64 = 0;
    let mut i: u64 = 0;
    
    while i < n
        invariant 
            i <= n,
            r == R(i as nat),
            r <= i * (i + 1) / 2,
            r <= u64::MAX,
        decreases n - i
    {
        proof {
            R_bounded(i as nat);
            assert(r <= i * (i + 1) / 2);
        }
        
        let prev_r = r;
        i = i + 1;
        
        proof {
            R_bounded(i as nat);
            assert(R(i as nat) <= i * (i + 1) / 2);
        }
        
        if prev_r > i {
            r = prev_r - i;
            proof {
                assert(i > 0);
                assert((i - 1) as nat == (i as nat) - 1);
                assert(R((i - 1) as nat) == prev_r);
                assert(prev_r > i);
                assert(R((i - 1) as nat) > i as nat);
                assert(R(i as nat) == (R((i - 1) as nat) - (i as nat)) as nat);
                assert(R(i as nat) == (prev_r - i) as nat);
                assert(r == R(i as nat));
            }
        } else {
            proof {
                assert(prev_r + i <= i * (i + 1) / 2) by {
                    R_bounded(i as nat);
                    assert(R(i as nat) <= i * (i + 1) / 2);
                    if i == 0 {
                        assert(prev_r == 0);
                        assert(prev_r + i == 0);
                    } else {
                        assert((i - 1) as nat == (i as nat) - 1);
                        assert(R((i - 1) as nat) == prev_r);
                        assert(prev_r <= i);
                        assert(R((i - 1) as nat) <= i as nat);
                        assert(R(i as nat) == R((i - 1) as nat) + (i as nat));
                        assert(R(i as nat) == prev_r + i);
                    }
                }
                assert(i * (i + 1) / 2 <= u64::MAX) by {
                    assert(i <= n);
                    assert(n <= u64::MAX);
                    assert(i * (i + 1) / 2 <= n * (n + 1) / 2);
                    assert(n * (n + 1) / 2 <= u64::MAX);
                }
                assert(prev_r + i <= i * (i + 1) / 2);
                assert(prev_r + i <= u64::MAX);
            }
            r = prev_r + i;
            proof {
                if i == 0 {
                    assert(prev_r == 0);
                    assert(r == 0);
                    assert(R(0) == 0);
                    assert(r == R(i as nat));
                } else {
                    assert((i - 1) as nat == (i as nat) - 1);
                    assert(R((i - 1) as nat) == prev_r);
                    assert(prev_r <= i);
                    assert(R((i - 1) as nat) <= i as nat);
                    assert(R(i as nat) == R((i - 1) as nat) + (i as nat));
                    assert(R(i as nat) == prev_r + i);
                    assert(r == R(i as nat));
                }
            }
        }
        
        proof {
            assert(r == R(i as nat));
            R_bounded(i as nat);
            assert(r <= i * (i + 1) / 2);
            assert(r <= u64::MAX);
        }
    }
    
    assert(i == n);
    assert(r == R(n as nat));
    r
}
// </vc-code>

fn main() {}

}