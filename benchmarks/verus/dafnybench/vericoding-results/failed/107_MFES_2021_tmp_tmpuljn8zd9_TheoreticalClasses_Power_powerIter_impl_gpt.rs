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
proof fn lemma_power_decr(x: int, n: nat)
    requires
        n > 0,
    ensures
        power(x, n) == x * power(x, (n - 1) as nat),
{
    reveal_with_fuel(power, 1);
    assert(power(x, n) == if n == 0 { 1 } else { x * power(x, (n - 1) as nat) });
    assert(power(x, n) == x * power(x, (n - 1) as nat));
}
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut res: i64 = 1;
    let mut i: u64 = n;

    while i > 0
        invariant
            i <= n,
            (res as int) * power(x as int, i as nat) == power(x as int, n as nat),
        decreases i
    {
        let new_res = res * x;
        let new_i: u64 = i - 1;

        proof {
            lemma_power_decr(x as int, i as nat);
            assert(power(x as int, i as nat) == (x as int) * power(x as int, new_i as nat));
        }

        res = new_res;
        i = new_i;
    }

    res
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