use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Specification function for GCD
spec fn gcd(a: int, b: int) -> int
    recommends a > 0 && b >= 0
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

// Lemma for the base case
proof fn lemma_gcd_base_case(a: int)
    requires a > 0
    ensures gcd(a, 0) == a
{
    // This follows directly from the definition of gcd
    assert(gcd(a, 0) == a);
}

// Lemma: GCD remains the same after one step of Euclidean algorithm
proof fn lemma_gcd_step(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
{
    // This follows directly from the definition of the gcd spec function
    assert(gcd(a, b) == gcd(b, a % b));
}

// Lemma: a % b has the right bounds when b > 0
proof fn lemma_mod_bounds(a: int, b: int)
    requires b > 0
    ensures a % b < b && a % b >= -b + 1
{
    // This is a fundamental property of modulo in Verus/Rust
}

fn gcdI(m: int, n: int) -> (g: int)
    requires
        m > 0 && n > 0
    ensures
        g == gcd(m, n)
{
    let mut a = m;
    let mut b = n;
    
    while b != 0
        invariant
            gcd(a, b) == gcd(m, n),
            a > 0,
            b >= 0
        decreases b
    {
        proof {
            lemma_mod_bounds(a, b);
            assert(a % b < b);
            assert(b > 0);  // from loop condition b != 0 and invariant b >= 0
        }
        
        let temp = a % b;
        
        proof {
            lemma_gcd_step(a, b);
            assert(gcd(a, b) == gcd(b, temp));
            // Since gcd(a, b) == gcd(m, n) by invariant
            assert(gcd(b, temp) == gcd(m, n));
        }
        
        // Handle the case where temp might be negative
        let next_b = if temp >= 0 { 
            temp 
        } else { 
            // Make it positive by adding b
            temp + b 
        };
        
        proof {
            if temp >= 0 {
                assert(next_b == temp);
                assert(0 <= next_b);
                assert(next_b < b);
            } else {
                assert(next_b == temp + b);
                assert(temp >= -b + 1);  // from lemma_mod_bounds
                assert(next_b >= -b + 1 + b);
                assert(next_b >= 1);
                assert(next_b > 0);
                assert(temp < 0);
                assert(next_b < b);
                assert(0 < next_b < b);
                
                // For negative modulo, gcd(b, temp) == gcd(b, temp + b)
                // This is because temp ≡ temp + b (mod b), so they have the same divisors
                // The key insight is that gcd(x, y) = gcd(x, y mod x) regardless of sign
                // Since temp = a % b, we have a = qb + temp for some q
                // So gcd(b, temp) = gcd(b, temp + b) by the fundamental GCD property
                assert(gcd(b, temp) == gcd(b, next_b));
            }
        }
        
        a = b;
        b = next_b;
    }
    
    proof {
        assert(b == 0);
        lemma_gcd_base_case(a);
        assert(gcd(a, 0) == a);
        assert(gcd(a, b) == a);
        // By invariant: gcd(a, b) == gcd(m, n)
        assert(a == gcd(m, n));
    }
    
    a
}

}