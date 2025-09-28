use vstd::prelude::*;

verus! {

/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n-1) as nat) }
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
proof fn power_mult_lemma(x: int, n: nat, m: nat)
    requires m <= n,
    ensures power(x, m) * power(x, n - m) == power(x, n)
    decreases n
{
    if m == 0 {
        assert(power(x, m) == 1);
    } else if m == n {
        assert(power(x, n - m) == 1);
    } else {
        assert(power(x, n) == x * power(x, n - 1));
        power_mult_lemma(x, m - 1, n - 1);
    }
}

proof fn power_double_lemma(x: int, n: nat)
    ensures power(x, 2 * n) == power(x, n) * power(x, n)
{
    power_mult_lemma(x, n, 2 * n);
}

proof fn power_square_lemma(x: int, n: nat)
    ensures power(x, n * n) == power(power(x, n), n)
    decreases n
{
    if n == 0 {
        assert(power(x, n * n) == 1);
    } else {
        assert(power(x, n * n) == x * power(x, n * n - 1));
        assert(power(power(x, n), n) == power(x, n) * power(power(x, n), n - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut acc: i32 = 1;
    let mut base: i32 = b;
    let mut exponent: u32 = n;
    while 0 < exponent
        invariant {
            0 <= exponent <= n,
            (acc as int) * power(base as int, exponent as nat) == power(b as int, n as nat)
        }
        decreases exponent
    {
        if exponent % 2 == 0 {
            let even_exponent = exponent / 2;
            proof {
                power_double_lemma(base as int, even_exponent as nat);
            }
            base = base * base;
            exponent = even_exponent;
        } else {
            let odd_exponent = exponent - 1;
            proof {
                power_mult_lemma(base as int, odd_exponent as nat, exponent as nat);
            }
            acc = acc * base;
            exponent = odd_exponent;
        }
    }
    acc
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}