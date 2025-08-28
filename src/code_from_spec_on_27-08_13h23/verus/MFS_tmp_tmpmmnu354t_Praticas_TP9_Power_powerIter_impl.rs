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
proof fn power_iter_helper(b: int, n: nat, current: int, iter: nat)
    requires
        current == power(b, iter),
        iter <= n,
    ensures
        power(b, n) == power(b, n - iter) * current,
    decreases n - iter
{
    if iter == n {
        assert(power(b, n - iter) == power(b, 0) == 1);
        assert(power(b, n) == current);
    } else {
        let next_iter = iter + 1;
        assert(power(b, next_iter) == b * power(b, iter));
        assert(power(b, n) == b * power(b, n - 1));
        power_iter_helper(b, n, current * b, next_iter);
        assert(power(b, n - iter) == b * power(b, n - next_iter));
        assert(power(b, n - iter) * current == power(b, n - next_iter) * (b * current));
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
{
    let mut result = 1i32;
    let mut i = 0u32;
    
    while i < n
        invariant
            i <= n,
            result as int == power(b as int, i as nat)
    {
        result = result * b;
        i = i + 1;
    }
    
    proof {
        power_iter_helper(b as int, n as nat, result as int, i as nat);
    }
    
    result
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}