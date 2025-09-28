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
proof fn lemma_power_zero(x: int)
    ensures power(x, 0) == 1
{}

proof fn lemma_power_step(x: int, n: nat)
    requires n >= 1
    ensures power(x, n) == x * power(x, (n - 1) as nat)
{}

proof fn lemma_power_one(x: int)
    ensures power(x, 1) == x
{
    assert(power(x, 1) == x * power(x, 0));
    lemma_power_zero(x);
}

spec fn power_iter_invariant(b: int, n: nat, i: nat, p: int) -> bool {
    &&& i <= n
    &&& p == power(b, i)
}

proof fn lemma_mul_no_overflow(a: i32, b: i32)
    requires
        a != 0,
        b != 0,
        |a as int| * |b as int| <= 0x7FFFFFFF,
    ensures
        (a * b) as int == a as int * b as int
{}
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
            p as int == power(b as int, i as nat),
        decreases (n - i) as int
    {
        assert(i < n);
        proof {
            lemma_power_step(b as int, (i + 1) as nat);
        }
        let temp_p: i32 = p;
        proof {
            lemma_mul_no_overflow(temp_p, b);
        }
        p = temp_p * b;
        proof {
            assert(temp_p as int == power(b as int, i as nat)) by { };
            assert(p as int == temp_p as int * (b as int)) by { };
            assert(p as int == power(b as int, i as nat) * (b as int)) by { };
            assert(power(b as int, (i + 1) as nat) == (b as int) * power(b as int, i as nat)) by {
                lemma_power_step(b as int, (i + 1) as nat);
            };
        }
        i = i + 1;
        proof {
            assert(i as nat == (i - 1 + 1) as nat);
        }
    }
    
    p
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.

fn main() {}

}