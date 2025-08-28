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
proof fn power_unfold(x: int, n: nat)
    requires n > 0
    ensures power(x, n) == x * power(x, (n-1) as nat)
{
}

proof fn power_zero(x: int)
    ensures power(x, 0) == 1
{
}

proof fn power_one(x: int)
    ensures power(x, 1) == x
{
    power_unfold(x, 1);
    power_zero(x);
}

proof fn power_step(x: int, i: nat)
    ensures power(x, (i + 1) as nat) == x * power(x, i)
{
    if i == 0 {
        power_zero(x);
    } else {
        power_unfold(x, (i + 1) as nat);
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
{
    let mut result: i32 = 1;
    let mut i: u32 = 0;
    let base = b;
    let exp = n;
    
    while i < exp
        invariant
            i <= exp,
            result as int == power(base as int, i as nat),
            result.abs() <= i32::MAX
        decreases exp - i
    {
        proof {
            power_step(base as int, i as nat);
        }
        result = result * base;
        i = i + 1;
    }
    
    result
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}