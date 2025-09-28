use vstd::prelude::*;

verus! {

/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of an integer (x^n), 
* illustrating the usage of lemmas and automatic induction in Verus.
* Translated from Dafny to Verus.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
}

// Computation of x^n in time and space O(log n).

// <vc-helpers>
// Lemma: power(x, 2*k) = power(x, k) * power(x, k)
proof fn lemma_power_double(x: int, k: nat)
    ensures power(x, 2 * k) == power(x, k) * power(x, k)
    decreases k
{
    if k == 0 {
        assert(power(x, 0) == 1);
        assert(2 * k == 0);
        assert(power(x, 2 * k) == 1);
        assert(power(x, k) * power(x, k) == 1 * 1);
    } else {
        assert(2 * k >= 2);
        assert(power(x, 2 * k) == x * power(x, (2 * k - 1) as nat));
        assert((2 * k - 1) as nat == (2 * (k - 1) + 1) as nat);
        assert(power(x, (2 * k - 1) as nat) == power(x, (2 * (k - 1) + 1) as nat));
        assert(power(x, (2 * (k - 1) + 1) as nat) == x * power(x, (2 * (k - 1)) as nat));
        lemma_power_double(x, (k - 1) as nat);
        assert(power(x, (2 * (k - 1)) as nat) == power(x, (k - 1) as nat) * power(x, (k - 1) as nat));
        
        assert(power(x, (2 * k - 1) as nat) == x * power(x, (2 * (k - 1)) as nat));
        assert(power(x, (2 * (k - 1)) as nat) == power(x, (k - 1) as nat) * power(x, (k - 1) as nat));
        assert(power(x, (2 * k - 1) as nat) == x * power(x, (k - 1) as nat) * power(x, (k - 1) as nat));
        
        assert(power(x, 2 * k) == x * power(x, (2 * k - 1) as nat));
        assert(power(x, 2 * k) == x * (x * power(x, (k - 1) as nat) * power(x, (k - 1) as nat)));
        assert(power(x, 2 * k) == x * x * power(x, (k - 1) as nat) * power(x, (k - 1) as nat));
        
        assert(power(x, k) == x * power(x, (k - 1) as nat));
        assert(power(x, k) * power(x, k) == (x * power(x, (k - 1) as nat)) * (x * power(x, (k - 1) as nat)));
        assert(power(x, k) * power(x, k) == x * x * power(x, (k - 1) as nat) * power(x, (k - 1) as nat));
    }
}

// Lemma: power(x, 2*k+1) = x * power(x, k) * power(x, k)
proof fn lemma_power_odd(x: int, k: nat)
    ensures power(x, 2 * k + 1) == x * power(x, k) * power(x, k)
    decreases k
{
    assert(power(x, 2 * k + 1) == x * power(x, (2 * k) as nat));
    lemma_power_double(x, k);
    assert(power(x, (2 * k) as nat) == power(x, k) * power(x, k));
    assert(power(x, 2 * k + 1) == x * (power(x, k) * power(x, k)));
    assert(power(x, 2 * k + 1) == x * power(x, k) * power(x, k));
}

// Lemma: power(a*a, k) = power(a, 2*k)
proof fn lemma_power_square(a: int, k: nat)
    ensures power(a * a, k) == power(a, 2 * k)
    decreases k
{
    if k == 0 {
        assert(power(a * a, 0) == 1);
        assert(power(a, 0) == 1);
    } else {
        assert(power(a * a, k) == (a * a) * power(a * a, (k - 1) as nat));
        lemma_power_square(a, (k - 1) as nat);
        assert(power(a * a, (k - 1) as nat) == power(a, 2 * (k - 1)) as nat);
        assert(power(a * a, k) == (a * a) * power(a, (2 * (k - 1)) as nat));
        assert(power(a, 2 * k) == power(a, 2 * (k - 1) + 2));
        assert(power(a, 2 * (k - 1) + 2) == a * power(a, (2 * (k - 1) + 1) as nat));
        assert(power(a, (2 * (k - 1) + 1) as nat) == a * power(a, (2 * (k - 1)) as nat));
        assert(power(a, 2 * k) == a * a * power(a, (2 * (k - 1)) as nat));
        assert(power(a, 2 * k) == (a * a) * power(a, (2 * (k - 1)) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 1;
    }
    
    let mut result: i64 = 1;
    let mut base: i64 = x;
    let mut exp: u64 = n;
    
    while exp > 0
        invariant 
            result as int * power(base as int, exp as nat) == power(x as int, n as nat),
            exp <= n
        decreases exp
    {
        if exp % 2 == 1 {
            result = result * base;
            exp = exp - 1;
            
            proof {
                let old_exp = exp + 1;
                lemma_power_odd(base as int, (exp / 2) as nat);
                assert(old_exp == 2 * (exp / 2) + 1);
                assert(power(base as int, old_exp as nat) == base as int * power(base as int, (exp / 2) as nat) * power(base as int, (exp / 2) as nat));
                assert(exp == 2 * (exp / 2));
                lemma_power_double(base as int, (exp / 2) as nat);
                assert(power(base as int, exp as nat) == power(base as int, (exp / 2) as nat) * power(base as int, (exp / 2) as nat));
            }
        } else {
            let old_base = base;
            base = base * base;
            exp = exp / 2;
            
            proof {
                let old_exp = exp * 2;
                lemma_power_double(old_base as int, exp as nat);
                assert(power(old_base as int, old_exp as nat) == power(old_base as int, exp as nat) * power(old_base as int, exp as nat));
                lemma_power_square(old_base as int, exp as nat);
                assert(power(old_base as int * old_base as int, exp as nat) == power(old_base as int, 2 * exp));
                assert(base as int == old_base as int * old_base as int);
                assert(power(base as int, exp as nat) == power(old_base as int, old_exp as nat));
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}