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
fn power_iter_helper(x: i64, n: u64, current: i64, i: u64) -> (p: i64)
    requires 0 <= i && i <= n
    ensures p * power(x as int, (n - i) as nat) == current * power(x as int, n as nat)
    decreases n - i
{
    if i < n {
        power_iter_helper(x, n, current * x, i + 1)
    } else {
        current
    }
}
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    power_iter_helper(x, n, 1, 0)
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