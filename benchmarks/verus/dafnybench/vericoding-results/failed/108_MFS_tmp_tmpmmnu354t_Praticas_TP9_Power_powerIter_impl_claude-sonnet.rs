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
proof fn power_iter_lemma(b: int, n: nat, acc: int, remaining: nat)
    requires remaining <= n
    ensures power(b, n) == acc * power(b, remaining)
    decreases remaining
{
    if remaining == 0 {
        assert(power(b, 0) == 1);
        assert(acc * power(b, 0) == acc * 1);
        assert(acc * 1 == acc);
        assert(power(b, n) == acc);
    } else {
        assert(power(b, remaining) == b * power(b, (remaining - 1) as nat));
        power_iter_lemma(b, n, acc * b, (remaining - 1) as nat);
        assert(power(b, n) == (acc * b) * power(b, (remaining - 1) as nat));
        assert((acc * b) * power(b, (remaining - 1) as nat) == acc * (b * power(b, (remaining - 1) as nat)));
        assert(b * power(b, (remaining - 1) as nat) == power(b, remaining));
        assert(acc * (b * power(b, (remaining - 1) as nat)) == acc * power(b, remaining));
    }
}
// </vc-helpers>

// <vc-spec>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut result: i32 = 1;
    let mut i: u32 = 0;
    
    while i < n
        invariant 
            i <= n,
            result as int == power(b as int, i as nat)
        decreases n - i
    {
        proof {
            assert(power(b as int, (i + 1) as nat) == b as int * power(b as int, i as nat));
            assert(power(b as int, i as nat) == result as int);
            assert(power(b as int, (i + 1) as nat) == b as int * result as int);
        }
        i = i + 1;
        result = b * result;
    }
    
    result
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}