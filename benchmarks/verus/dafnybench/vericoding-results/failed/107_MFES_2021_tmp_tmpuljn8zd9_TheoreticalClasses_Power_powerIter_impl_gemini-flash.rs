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
lemma fn mult_power(x: int, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, (a + b) as nat)
    decreases a
{
    if a == 0 {
        assert(power(x, a) == 1);
        assert(power(x, a) * power(x, b) == 1 * power(x, b));
        assert(power(x, (a + b) as nat) == power(x, b));
    } else {
        assert(power(x, a) == x * power(x, (a - 1) as nat));
        assert(power(x, a) * power(x, b) == x * power(x, (a - 1) as nat) * power(x, b));
        mult_power(x, (a - 1) as nat, b);
        assert(power(x, (a - 1) as nat) * power(x, b) == power(x, ((a - 1) + b) as nat));
        assert(x * power(x, (a - 1) as nat) * power(x, b) == x * power(x, ((a - 1) + b) as nat));
        
        let a_plus_b_minus_1 = (a + b - 1) as nat;
        let a_minus_1_plus_b = ((a - 1) + b) as nat;

        // Since a and b are nat, a+b >= 1 if a > 0
        if a + b > 0 {
            assert(power(x, (a + b) as nat) == x * power(x, (a_plus_b_minus_1)));
            assert(a_plus_b_minus_1 == a_minus_1_plus_b);
        }
    }
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
            i <= n,
            p as int == power(x as int, i as nat),
        {
            p = p * x;
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