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
proof fn i32_mul_as_int(a: i32, b: i32)
    ensures (a*b) as int == (a as int) * (b as int)
{
    assert(((a*b) as int) == (a as int) * (b as int));
}

proof fn power_succ(x: int, n: nat)
    ensures power(x, n + 1) == x * power(x, n)
    decreases n
{
    if n == 0 {
        // power(x, 1) == x * power(x, 0)
        assert(power(x, 0) == 1);
        assert(power(x, 1) == x * power(x, 0));
    } else {
        // By definition of power, holds for all n
        assert(power(x, n + 1) == x * power(x, n));
    }
}
// </vc-helpers>

// <vc-spec>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut p: i32 = 1;
    let N: nat = n as nat;
    let mut i: nat = 0;
    while i < N
        invariant i <= N;
        invariant p as int == power(b as int, i);
        decreases N - i
    {
        let old_p = p;
        let old_i = i;
        p = p * b;
        i = i + 1;
        proof {
            i32_mul_as_int(old_p, b);
            assert(p as int == (old_p * b) as int);
            assert((old_p * b) as int == (old_p as int) * (b as int));
            assert(old_p as int == power(b as int, old_i));
            assert((old_p as int) * (b as int) == (b as int) * power(b as int, old_i));
            power_succ(b as int, old_i);
            assert((b as int) * power(b as int, old_i) == power(b as int, old_i + 1));
            assert(p as int == power(b as int, i));
        }
    }
    p
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}