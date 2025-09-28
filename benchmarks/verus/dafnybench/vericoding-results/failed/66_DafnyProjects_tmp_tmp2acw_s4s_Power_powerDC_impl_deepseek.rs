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
spec fn power_dc_spec(x: int, n: nat, p: int) -> bool
    decreases n
{
    if n == 0 {
        p == 1
    } else {
        let half_n = n / 2;
        if n % 2 == 0 {
            power_dc_spec(x * x, half_n, p)
        } else {
            power_dc_spec(x * x, half_n, p / x) && p % x == 0
        }
    }
}

proof fn power_dc_lemma(x: int, n: nat)
    ensures
        power_dc_spec(x, n, power(x, n)),
    decreases n
{
    if n > 0 {
        let half_n = n / 2;
        power_dc_lemma(x * x, half_n);
        if n % 2 == 1 {
            assert(power(x, n) == x * power(x * x, half_n)) by {
                reveal(power);
                if n >= 1 {
                    assert(power(x, n) == x * power(x, (n - 1) as nat));
                    assert((n - 1) == 2 * half_n);
                    assert(power(x, (n - 1) as nat) == power(x * x, half_n));
                }
            };
        } else {
            assert(power(x, n) == power(x * x, half_n)) by {
                reveal(power);
                if n >= 2 {
                    assert(power(x, n) == x * power(x, (n - 1) as nat));
                    assert((n - 1) == 2 * half_n - 1);
                    power_dc_lemma(x, (n - 1) as nat);
                    assert(power(x, (n - 1) as nat) == x * power(x * x, (half_n - 1) as nat));
                    assert(power(x, n) == x * x * power(x * x, (half_n - 1) as nat));
                    assert(power(x * x, half_n) == (x * x) * power(x * x, (half_n - 1) as nat));
                } else if n == 1 {
                    assert(false); // n cannot be 1 when %2==0
                }
            };
        }
    }
}

proof fn power_dc_complete(x: int, n: nat, p: int)
    requires
        power_dc_spec(x, n, p),
    ensures
        p == power(x, n),
    decreases n
{
    if n > 0 {
        let half_n = n / 2;
        if n % 2 == 0 {
            power_dc_complete(x * x, half_n, p);
            assert(power(x, n) == power(x * x, half_n)) by {
                reveal(power);
                if n >= 2 {
                    assert(power(x, n) == x * power(x, (n - 1) as nat));
                    assert((n - 1) == 2 * half_n - 1);
                    power_dc_lemma(x, (n - 1) as nat);
                    assert(power(x, (n - 1) as nat) == x * power(x * x, (half_n - 1) as nat));
                    assert(power(x, n) == x * x * power(x * x, (half_n - 1) as nat));
                    assert(power(x * x, half_n) == (x * x) * power(x * x, (half_n - 1) as nat));
                }
            };
        } else {
            power_dc_complete(x * x, half_n, p / x);
            assert(p == x * (p / x));
            assert(power(x, n) == x * power(x * x, half_n)) by {
                reveal(power);
                if n >= 1 {
                    assert(power(x, n) == x * power(x, (n - 1) as nat));
                    assert((n - 1) == 2 * half_n);
                    assert(power(x, (n - 1) as nat) == power(x * x, half_n));
                }
            };
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut p: i64 = 1;
    let mut base = x;
    let mut exponent = n;
    
    proof {
        power_dc_lemma(x as int, n as nat);
    }
    
    while exponent > 0
        invariant
            exponent <= n,
            power_dc_spec(x as int, n as nat, (p as int * power(base as int, exponent as nat))),
        decreases exponent
    {
        if exponent % 2 == 1 {
            p = p * base;
        }
        base = base * base;
        exponent = exponent / 2;
    }
    
    proof {
        power_dc_complete(x as int, n as nat, p as int);
    }
    
    p
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}