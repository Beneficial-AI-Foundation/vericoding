// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * power(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added explicit modular arithmetic proof */
proof fn lemma_power_mod(n: nat, p: int)
    requires
        n > 0,
        p > 0,
    ensures
        power(2, n) % p == ((power(2, (n - 1) as nat) % p) * 2) % p,
    decreases n
{
    // By definition: power(2, n) = 2 * power(2, n-1)
    assert(power(2, n) == 2 * power(2, (n - 1) as nat));
    
    let a = power(2, (n - 1) as nat);
    let a_mod = a % p;
    
    // We need to show: (2*a) % p == ((a % p) * 2) % p
    // This is true because for any integers x, y, m:
    // (x * y) % m == ((x % m) * (y % m)) % m
    // In our case: (2 * a) % p == ((2 % p) * (a % p)) % p == (2 * (a % p)) % p
    
    // The modular arithmetic property holds by SMT reasoning
    assert((2 * a) % p == (2 * a_mod) % p);
}
// </vc-helpers>

// <vc-spec>
fn modp(n: i8, p: i8) -> (result: i8)
    requires 
        n >= 0 && p > 0,
    ensures 
        result >= 0 && result < p,
        result as int == power(2, n as nat) % (p as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed variable tracking in assertions */
    let mut ret: i8 = 1 % p;  // power(2, 0) = 1
    let mut i: i8 = 0;
    
    // Handle initial case
    if n == 0 {
        return ret;
    }
    
    while i < n
        invariant
            0 <= i <= n,
            p > 0,
            0 <= ret < p,
            ret as int == power(2, i as nat) % (p as int),
        decreases n - i
    {
        let old_ret = ret;
        
        proof {
            if i + 1 <= n {
                lemma_power_mod((i + 1) as nat, p as int);
            }
        }
        
        // Calculate (ret * 2) % p safely using i16 to avoid overflow
        // Since ret < p <= 127, ret * 2 < 254, which fits in i16
        let doubled: i16 = (old_ret as i16) * 2;
        let doubled_mod: i16 = doubled % (p as i16);
        
        // Ensure the result fits in i8
        assert(0 <= doubled_mod < p as i16) by {
            assert(0 <= old_ret < p);
            assert(doubled_mod == doubled % (p as i16));
            assert(0 <= doubled_mod < p as i16);
        }
        
        ret = doubled_mod as i8;
        i = i + 1;
        
        assert(ret as int == power(2, i as nat) % (p as int)) by {
            assert(old_ret as int == power(2, (i - 1) as nat) % (p as int));
            assert(ret as int == doubled_mod as int);
            assert(doubled_mod as int == ((old_ret as int * 2) % (p as int)));
            lemma_power_mod(i as nat, p as int);
            assert(power(2, i as nat) % (p as int) == ((power(2, (i - 1) as nat) % (p as int)) * 2) % (p as int));
            assert(power(2, i as nat) % (p as int) == ((old_ret as int) * 2) % (p as int));
        }
    }
    
    ret
}
// </vc-code>


}

fn main() {}