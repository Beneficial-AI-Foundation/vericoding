use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish that if mid * mid > n, then the square root is less than mid
proof fn lemma_square_monotonic(a: u32, b: u32)
    requires a <= b
    ensures a * a <= b * b
{
    // Proof by arithmetic reasoning
    assert(a * a <= b * b) by {
        assert(0 <= a <= b);
        assert(a * a <= a * b) by {
            assert(a * a == a * a);
            assert(a <= b);
            assert(a * a <= a * b) by(nonlinear_arith)
                requires a <= b, 0 <= a;
        }
        assert(a * b <= b * b) by {
            assert(a <= b);
            assert(a * b <= b * b) by(nonlinear_arith)
                requires a <= b, 0 <= b;
        }
    }
}

// Helper to prevent overflow in multiplication
proof fn lemma_mult_overflow_check(a: u32, b: u32) 
    requires a <= 65535, b <= 65535
    ensures (a as int) * (b as int) <= u32::MAX as int
{
    assert((a as int) * (b as int) <= 65535 * 65535) by(nonlinear_arith)
        requires a <= 65535, b <= 65535;
    assert(65535 * 65535 == 4294836225);
    assert(4294836225 < 4294967296);
    assert(u32::MAX == 4294967295);
}

// Helper lemma for the special case when result is 65535
proof fn lemma_65535_is_max_sqrt(n: u32)
    requires 65535 * 65535 <= n
    ensures 65535 * 65535 <= n < (65536 as int) * (65536 as int)
{
    assert(65535 * 65535 == 4294836225);
    assert((65536 as int) * (65536 as int) == 4294967296);
    assert(n <= u32::MAX);
    assert(u32::MAX == 4294967295);
    assert(4294836225 <= n <= 4294967295);
    assert(n < 4294967296);
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    let mut low: u32 = 0;
    let mut high: u32 = if n >= 65536 { 65535 } else { n };
    let mut result: u32 = 0;
    
    // Establish initial invariants
    assert(result * result <= n);
    assert(high <= 65535);
    
    // For the initial forall invariants
    assert(forall|x: u32| x > high && x <= 65535 ==> #[trigger] (x * x) > n) by {
        assert forall|x: u32| x > high && x <= 65535 implies #[trigger] (x * x) > n by {
            if n >= 65536 {
                assert(high == 65535);
                // No x > 65535 && x <= 65535
            } else {
                assert(high == n);
                assert(x > n);
                assert(x * x >= (n + 1) * (n + 1)) by(nonlinear_arith)
                    requires x >= n + 1;
                assert((n + 1) * (n + 1) > n) by(nonlinear_arith)
                    requires n >= 0;
            }
        }
    }
    
    while low <= high
        invariant 
            result * result <= n,
            high <= 65535,
            low <= high ==> forall|x: u32| #[trigger] (x * x) <= n && x < low ==> x <= result,
            low <= high ==> forall|x: u32| x > high && x <= 65535 ==> #[trigger] (x * x) > n,
            low > high ==> result * result <= n < (result + 1) * (result + 1),
        decreases high - low + 1,
    {
        let mid = low + (high - low) / 2;
        
        proof {
            lemma_mult_overflow_check(mid, mid);
            assert(mid <= high);
            assert(high <= 65535);
            assert(mid <= 65535);
        }
        
        if mid * mid <= n {
            result = mid;
            let old_low = low;
            let old_high = high;
            
            if mid == 65535 {
                // Special case: mid is the maximum possible value
                assert(result == 65535);
                assert(65535 * 65535 <= n);
                proof {
                    lemma_65535_is_max_sqrt(n);
                    assert(65535 * 65535 <= n < (65536 as int) * (65536 as int));
                }
                return result;
            }
            
            // Check if we found the exact answer
            proof {
                lemma_mult_overflow_check((mid + 1) as u32, (mid + 1) as u32);
            }
            if (mid + 1) * (mid + 1) > n {
                assert(result * result <= n);
                assert((result + 1) * (result + 1) > n);
                return result;
            }
            
            low = mid + 1;
            
            // Preserve invariants
            assert(result * result <= n);
            if low <= high {
                assert forall|x: u32| #[trigger] (x * x) <= n && x < low implies x <= result by {
                    assert forall|x: u32| #[trigger] (x * x) <= n && x < low implies x <= result by {
                        if x < old_low {
                            // From old invariant
                            assert(x <= result);
                        } else {
                            assert(old_low <= x < low);
                            assert(x <= mid);
                            assert(x <= result);
                        }
                    }
                }
            }
        } else {
            // mid * mid > n
            if mid == 0 {
                assert(0 * 0 == 0);
                assert(0 <= n);
                assert(false); // contradiction
                return 0;
            }
            let old_high = high;
            high = mid - 1;
            
            // Preserve invariants
            if low <= high {
                assert forall|x: u32| x > high && x <= 65535 implies #[trigger] (x * x) > n by {
                    assert forall|x: u32| x > high && x <= 65535 implies #[trigger] (x * x) > n by {
                        if x > old_high {
                            // From old invariant
                            assert(x * x > n);
                        } else {
                            assert(high < x <= old_high);
                            assert(mid <= x);
                            lemma_square_monotonic(mid, x);
                            assert(mid * mid <= x * x);
                            assert(mid * mid > n);
                            assert(x * x > n);
                        }
                    }
                }
            }
        }
    }
    
    assert(low > high);
    assert(result * result <= n < (result + 1) * (result + 1));
    result
}
// </vc-code>

fn main() {}

}