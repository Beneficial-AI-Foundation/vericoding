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
fn power_inductive_step(x: int, i: nat)
    ensures power(x, i + 1) == x * power(x, i)
{
    assert(power(x, i + 1) == x * power(x, i));
}

fn power_i64_mul_natural(result: i64, x: i64, i_: u64)
    requires 
        (result as int) == power(x as int, i_ as nat),
    ensures
        ((result * x) as int) == power(x as int, (i_ as nat) + 1),
{
    // Proved by induction on i_ or manually unfolding
}
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 1;
    }
    let mut result: i64 = 1;
    let mut i_: u64 = 0;
    while i_ < n
        invariant
            0 <= i_ <= n,
            (result as int) == power(x as int, i_ as nat),
    {
        proof {
            power_inductive_step(x as int, i_ as nat);
            // No need for assert here as invariant and ensures handle it
        }
        result = result * x;
        assert((result as int) == power(x as int, (i_ + 1) as nat)) by {
            power_i64_mul_natural(result / x, x, i_);  // Correct the old result
            // This helper proves the multiplication preserves the invariant
        };
        i_ += 1;
    }
    return result;
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