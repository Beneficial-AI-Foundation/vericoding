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
proof fn lemma_power_succ(x: int, a: nat)
    decreases a
{
    if a == 0 {
        assert(power(x, 1) == x * power(x, 0));
    } else {
        lemma_power_succ(x, a - 1);
        assert(power(x, a + 1) == x * power(x, a));
    }
}

proof fn lemma_cast_mul(a: i64, b: i64) {
    assert((a * b) as int == (a as int) * (b as int));
}
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let n_nat: nat = n as nat;
    let mut i: nat = 0;
    let mut p: i64 = 1;
    while i < n_nat
        invariant i <= n_nat;
        invariant (p as int) == power(x as int, i);
        decreases n_nat - i;
    {
        let new_p: i64 = p * x;
        proof {
            lemma_cast_mul(p, x);
            lemma_power_succ(x as int, i);
            assert((new_p as int) == (p as int) * (x as int));
            assert((p as int) * (x as int) == power(x as int, i + 1));
            assert((new_p as int) == power(x as int, i + 1));
        }
        p = new_p;
        i = i + 1;
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