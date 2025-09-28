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
proof fn lemma_power_succ(x: int, n: nat)
    ensures power(x, n + 1) == x * power(x, n)
{
    reveal(power);
}
// </vc-helpers>

// <vc-spec>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut p: i32 = 1;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            p as int == power(b as int, i as nat)
        decreases (n as nat) - (i as nat)
    {
        let i0 = i;
        let p0 = p;
        p = p * b;
        proof { lemma_power_succ(b as int, i0 as nat); }
        i = i + 1;
        assert(i as nat == (i0 as nat) + 1);
        assert(power(b as int, i as nat) == (b as int) * power(b as int, i0 as nat));
        assert(p as int == (p0 as int) * (b as int));
        assert(p as int == power(b as int, i as nat));
    }
    assert(i == n);
    assert(p as int == power(b as int, n as nat));
    p
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}