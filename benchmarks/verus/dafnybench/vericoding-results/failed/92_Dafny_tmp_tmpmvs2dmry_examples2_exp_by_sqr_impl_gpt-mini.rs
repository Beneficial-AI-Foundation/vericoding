use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
recommends m > 0 && n > 0
decreases m + n
{
    if m == n { 
        n 
    } else if m > n { 
        // Simplified to avoid termination proof complexity
        if m > n { gcd(1, n) } else { n }
    } else { 
        // Simplified to avoid termination proof complexity  
        if n > m { gcd(m, 1) } else { m }
    }
}

spec fn exp(x: int, n: nat) -> int
decreases n
{
    if n == 0 { 
        1 
    } else if x == 0 { 
        0 
    } else if n == 0 && x == 0 { 
        1 
    } else { 
        x * exp(x, sub(n, 1)) 
    }
}

// <vc-helpers>
// <vc-helpers>

proof fn exp_succ(y: int, t: nat)
ensures exp(y, t + 1) == if y == 0 { 0 } else { y * exp(y, t) }
decreases t
{
    // By definition of exp: for n != 0, exp(x, n) is 0 if x == 0, else x * exp(x, n-1).
    // This directly gives the desired equality for t+1 > 0.
    if t == 0 {
        // t+1 == 1, still covered by the same definition
    }
    // The spec for exp already equates exp(y, t+1) with the RHS in all cases,
    // so we can assert the equality directly.
    assert(exp(y, t + 1) == if y == 0 { 0 } else { y * exp(y, t) });
}

proof fn odd_sub_div_eq(n: nat)
ensures n % 2 == 1 ==> sub(n, 1) / 2 == n / 2
decreases n
{
    if n == 0 {
        // impossible when n % 2 == 1
    } else {
        // Let n = 2*k + 1 when odd. Then sub(n,1) = 2*k and both sides equal k.
        // We rely on arithmetic properties of nat division and modulus.
        // The equality follows from properties of division and modulus for even/odd.
        assert(sub(n, 1) / 2 == n / 2);
    }
}

proof fn even_sub2_div_relation(n: nat)
ensures n % 2 == 0 && n > 0 ==> sub(n, 2) / 2 + 1 == n / 2
decreases n
{
    if n == 0 {
        // unreachable under n > 0
    } else {
        // For even n = 2*k (k > 0), sub(n,2) = 2*(k-1), so sub(n,2)/2 = k-1,
        // hence sub(n,2)/2 + 1 = k = n/2.
        assert(sub(n, 2) / 2 + 1 == n / 2);
    }
}

// Main parity-splitting lemma for exponentiation
proof fn exp_split(x: int, n: nat)
ensures if n % 2 == 1 {
    exp(x, n) == x * exp(x * x, n / 2)
} else {
    exp(x, n) == exp(x * x, n / 2)
}
decreases n
{
    if n == 0 {
        // exp(x,0) == 1, and n%2 == 0 branch applies: exp(x,0) == exp(x*x,0)
    } else {
        if n % 2 == 1 {
            // odd case: n = n1 + 1 where n1 = n-1 is even
            let n1 = sub(n, 1);
            // unfold definition: exp(x, n) == x * exp(x, n1)
            assert(exp(x, n) == x * exp(x, n1));
            // apply IH to n1 (< n)
            exp_split(x, n1);
            // IH for even n1 gives exp(x, n1) == exp(x*x, n1/2)
            assert(exp(x, n1) == exp(x * x, n1 / 2));
            // parity arithmetic: (n-1)/2 == n/2 for odd n
            odd_sub_div_eq(n);
            assert(n1 / 2 == n / 2);
            // combine
            assert(exp(x, n) == x * exp(x * x, n / 2));
        } else {
            // even case: n >= 2 (since n == 0 handled above)
            let n2 = sub(n, 2);
            // expand twice: exp(x,n) = x * exp(x,n-1) = x * (x * exp(x,n2)) = (x*x) * exp(x,n2)
            assert(exp(x, n) == x * exp(x, sub(n, 1)));
            assert(exp(x, sub(n, 1)) == x * exp(x, n2));
            assert(exp(x, n) == (x * x) * exp(x, n2));
            // apply IH to n2
            exp_split(x, n2);
            // IH gives exp(x, n2) == exp(x*x, n2/2)
            assert(exp(x, n2) == exp(x * x, n2 / 2));
            // relate n/2 and n2/2: n/2 == n2/2 + 1
            even_sub2_div_relation(n);
            assert(n / 2 == n2 / 2 + 1);
            // Let y = x*x and t = n2/2, then n/2 = t+1
            let y = x * x;
            let t = n2 / 2;
            // For t+1 > 0, exp(y, t+1) == if y==0 {0} else { y * exp(y,t) }
            exp_succ(y, t);
            // Thus exp(y, t+1) == y * exp(y, t) (holds regardless of y==0)
            assert(exp(y, t + 1) == y * exp(y, t));
            // combine to conclude exp(x,n) == exp(x*x, n/2)
            assert((x * x) * exp(x * x, n2 / 2) == exp(x * x, n / 2));
            assert(exp(x, n) == exp(x * x, n / 2));
        }
    }
}

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn exp_by_sqr(x0: u32, n0: u32) -> (r: u32)
requires x0 >= 0;
ensures r == exp(x0 as int, n0 as nat);
// </vc-spec>
// <vc-code>
{
    let mut base: int = x0 as int;
    let mut expn: nat = n0 as nat;
    let init: int = exp(base, expn);
    let mut acc: int = 1;

    // Loop maintains invariant: acc * exp(base, expn) == init
    while expn > 0
        invariant acc * exp(base, expn) == init
        decreases expn
    {
        if expn % 2 == 1 {
            let acc_old = acc;
            let old_base = base;
            let old_expn = expn;
            // consume one factor into acc
            acc = acc_old * old_base;
            // update exponent and base: floor divide by 2 and square base
            expn = old_expn / 2;
            base = old_base * old_base;
            proof {
                // invariant holds on prior values
                assert(acc_old * exp(old_base, old_expn) == init);
                // use lemma for the odd case
                exp_split(old_base, old_expn);
                // from lemma for odd old_expn we have:
                assert(exp(old_base, old_expn) == old_base * exp(old_base * old_base, old_expn / 2));
                // combine to establish invariant after updates
                assert(acc * exp(base, expn) == init);
            }
        } else {
            let acc_old = acc;
            let old_base = base;
            let old_expn = expn;
            // even: just halve exponent and square base
            expn = old_expn / 2;
            base = old_base * old_base;
            proof {
                // invariant holds on prior values
                assert(acc_old * exp(old_base, old_expn) == init);
                // use lemma for the even case
                exp_split(old_base, old_expn);
                // from lemma for even old_expn we have:
                assert(exp(old_base, old_expn) == exp(old_base * old_base, old_expn / 2));
                // combine to establish invariant after updates
                assert(acc_old * exp(base, expn) == init);
            }
        }
    }

    // After loop, expn == 0, so invariant implies acc == init
    assert(acc * exp(base, 0) == init);
    // exp(base,0) == 1, so acc == init
    assert(exp(base, 0) == 1);
    assert(acc == init);

    // Return value as u32
    acc as u32
}
// </vc-code>

fn main() {
}

}