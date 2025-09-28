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
// Lemma to help prove that multiplying by b one more time gives us the next power
proof fn power_step(x: int, n: nat)
    ensures power(x, n + 1) == x * power(x, n)
{
    // This follows directly from the definition of power
    // power(x, n+1) = x * power(x, n) by definition
}

// Lemma showing that power(x, 0) = 1
proof fn power_zero(x: int)
    ensures power(x, 0) == 1
{
    // This follows directly from the definition of power
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
            0 <= i <= n,
            p as int == power(b as int, i as nat),
        decreases n - i,
    {
        let old_i = i;
        let old_p = p;
        
        // Update both p and i together to maintain invariant
        i = i + 1;
        p = p * b; // Use regular multiplication
        
        proof {
            // Prove that the invariant is maintained
            // old_p == power(b, old_i) by invariant
            // new_p == old_p * b == power(b, old_i) * b == power(b, old_i + 1) == power(b, new_i)
            assert(old_p as int == power(b as int, old_i as nat));
            assert(i == old_i + 1);
            power_step(b as int, old_i as nat);
            assert(power(b as int, (old_i + 1) as nat) == (b as int) * power(b as int, old_i as nat));
            assert(p as int == power(b as int, i as nat));
        }
    }
    
    p
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}