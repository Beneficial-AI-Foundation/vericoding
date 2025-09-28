use vstd::prelude::*;

verus! {

/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
proof fn lemma_power_add(x: int, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, (a + b) as nat)
    decreases a
{
    if a == 0 {
        assert(power(x, 0) == 1);
        assert(power(x, (0 + b) as nat) == power(x, b));
    } else {
        let a_dec = (a - 1) as nat;
        lemma_power_add(x, a_dec, b);
        assert(power(x, a) == x * power(x, a_dec));
        assert(power(x, (a + b) as nat) == x * power(x, (a_dec + b) as nat));
    }
}

proof fn lemma_power_mult(x: int, a: nat, b: nat)
    ensures power(power(x, a), b) == power(x, (a * b) as nat)
    decreases b
{
    if b == 0 {
        assert(power(power(x, a), 0) == 1);
        assert(power(x, (a * 0) as nat) == power(x, 0));
    } else {
        let b_dec = (b - 1) as nat;
        lemma_power_mult(x, a, b_dec);
        assert(power(power(x, a), b) == power(x, a) * power(power(x, a), b_dec));
        assert(power(x, (a * b_dec) as nat) * power(x, a) == power(x, (a * b) as nat)) by {
            lemma_power_add(x, (a * b_dec) as nat, a);
            assert((a * b_dec) + a == a * b);
        }
    }
}

proof fn lemma_power_even(x: int, n: nat)
    requires n % 2 == 0
    ensures power(x, n) == power(x * x, (n / 2) as nat)
{
    lemma_power_add(x, (n/2) as nat, (n/2) as nat);
    assert(power(x, (n/2) as nat) * power(x, (n/2) as nat) == power(x, n));
    lemma_power_mult(x, 2, (n/2) as nat);
    assert(power(x * x, (n/2) as nat) == power(x, (2 * (n/2)) as nat));
    assert(2 * (n/2) == n) by {
        assert(n % 2 == 0);
    }
}

proof fn lemma_power_odd(x: int, n: nat)
    requires n % 2 == 1
    ensures power(x, n) == x * power(x * x, ((n - 1)/2) as nat)
{
    let n_dec = (n - 1) as nat;
    lemma_power_even(x, n_dec);
    assert(power(x, n_dec) == power(x * x, (n_dec/2) as nat));
    assert(power(x, n) == x * power(x, n_dec));
    assert((n_dec/2) == ((n - 1)/2));
}
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut p: i64 = 1;
    let mut i: u64 = 0;
    while i < n
        invariant
            0 <= i <= n,
            p == power(x as int, i as nat)
        decreases n - i
    {
        proof {
            let x_int = x as int;
            let i_nat = i as nat;
            lemma_power_add(x_int, i_nat, 1);
            assert(power(x_int, i_nat) * power(x_int, 1) == power(x_int, (i_nat + 1) as nat));
            assert(power(x_int, 1) == x_int);
            assert(p * x == power(x_int, i_nat) * x_int);
        }
        p = p * x;
        i = i + 1;
        proof {
            assert(i as nat == (i_nat + 1) as nat);
        }
    }
    p
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.

// A simple test case to make sure the specification is adequate.

fn main() {
}

}